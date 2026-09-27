import { createPublicClient, createWalletClient, http, isAddress, parseAbi, zeroAddress } from "viem";
import { bsc, base } from "viem/chains";
import { privateKeyToAccount } from "viem/accounts";
import {
  Connection,
  Keypair,
  PublicKey,
  Transaction,
} from "@solana/web3.js";
import {
  createAssociatedTokenAccountInstruction,
  createTransferInstruction,
  getAssociatedTokenAddress,
  getAccount,
  TOKEN_PROGRAM_ID,
  ASSOCIATED_TOKEN_PROGRAM_ID,
  unpackAccount,
} from "@solana/spl-token";
import bs58 from "bs58";
import nacl from "tweetnacl";

const API_URL = process.env.SETTLEMENT_API_URL ?? "http://127.0.0.1:8787";
const API_KEY = process.env.SETTLEMENT_API_KEY ?? "";
const LIVE = process.env.SETTLEMENT_LIVE === "true";
const ONCE = process.env.SETTLEMENT_ONCE === "true";
const INTERVAL_MS = Number(process.env.SETTLEMENT_POLL_MS ?? 3000);
// Maximum fills to attempt per poll cycle (fetched from API)
const POLL_LIMIT = Number(process.env.SETTLEMENT_POLL_LIMIT ?? 50);
const SETTLEMENT_NETWORK = String(process.env.SETTLEMENT_NETWORK ?? "").trim().toLowerCase();
const SETTLEMENT_PAIR_ID = String(process.env.SETTLEMENT_PAIR_ID ?? "").trim();
// Maximum fills per batch transaction (contract limit is 50)
const BATCH_SIZE = Math.min(Number(process.env.SETTLEMENT_BATCH_SIZE ?? 30), 50);
const SOLANA_BATCH_SIZE = Math.min(Math.max(1, Number(process.env.SOLANA_SETTLEMENT_BATCH_SIZE ?? 4)), 10);
const SOLANA_CONCURRENCY = Math.max(1, Number(process.env.SOLANA_SETTLEMENT_CONCURRENCY ?? 8));
const WORKER_ID = process.env.SETTLEMENT_WORKER_ID ?? `executor-${process.pid}-${crypto.randomUUID()}`;
const metrics = {
  polls: 0,
  claimed: 0,
  confirmed: 0,
  failed: 0,
  partial: 0,
  retries: 0,
  apiErrors: 0,
  startedAt: Date.now(),
};
const solanaAccountLocks = new Map();
const solanaDestinationCache = new Map();
function resolveUniqueConfigValue(values, label) {
  const cleanValues = values
    .map((value) => (typeof value === "string" ? value.trim() : ""))
    .filter(Boolean);
  const uniqueValues = [...new Set(cleanValues)];
  if (uniqueValues.length > 1) {
    throw new Error(
      `${label} is configured with conflicting values: ${uniqueValues.join(" | ")}. ` +
      "Use one canonical executor key across SOLANA_EXECUTOR_PRIVATE_KEY, DEVNET_EXECUTOR_PRIVATE_KEY, and SETTLEMENT_EXECUTOR_PRIVATE_KEY.",
    );
  }
  return uniqueValues[0] ?? "";
}
const privateKey = resolveUniqueConfigValue([
  process.env.SETTLEMENT_EXECUTOR_PRIVATE_KEY,
], "EVM executor private key");
const simulatorAddress = process.env.SETTLEMENT_SIMULATOR_ADDRESS;

if (!API_KEY) throw new Error("SETTLEMENT_API_KEY is required for settlement executor access");
if (LIVE && !privateKey) throw new Error("SETTLEMENT_EXECUTOR_PRIVATE_KEY is required when SETTLEMENT_LIVE=true");
if (!LIVE && !privateKey && !simulatorAddress) {
  throw new Error("Set SETTLEMENT_SIMULATOR_ADDRESS for simulation or SETTLEMENT_EXECUTOR_PRIVATE_KEY for live execution");
}

// ── Per-chain configuration ───────────────────────────────────────────────────

const CHAIN_CONFIG = {
  bsc: {
    chain: bsc,
    contract: process.env.SETTLEMENT_CONTRACT ?? "0x4896ebe3EE1436a58c690A8021301A6bFD6BD4E7",
    rpcUrls: (process.env.BSC_RPC_URLS ?? process.env.BSC_RPC_URL ?? "https://bsc-rpc.publicnode.com,https://bsc-dataseed.binance.org,https://bsc.blockrazor.xyz")
      .split(",").map((u) => u.trim()).filter(Boolean),
  },
  base: {
    chain: base,
    contract: process.env.BASE_SETTLEMENT_CONTRACT ?? "0x723da0ef5eea8370015465e9Cf2513D7e48e1b61",
    rpcUrls: (process.env.BASE_RPC_URLS ?? process.env.BASE_RPC_URL ?? "https://mainnet.base.org,https://base.llamarpc.com,https://base-rpc.publicnode.com")
      .split(",").map((u) => u.trim()).filter(Boolean),
  },
  robinhood: {
    chain: {
      id: Number(process.env.ROBINHOOD_CHAIN_ID ?? 4663),
      name: "Robinhood Chain",
      nativeCurrency: { name: "Ether", symbol: "ETH", decimals: 18 },
      rpcUrls: { default: { http: [(process.env.ROBINHOOD_RPC_URL ?? "https://robinhood-mainnet.core.chainstack.com/f8922de06dc48d17affa815a4cde9727")] } },
      blockExplorers: { default: { name: "Blockscout", url: "https://robinhoodchain.blockscout.com" } },
    },
    contract: String(process.env.ROBINHOOD_SETTLEMENT_CONTRACT ?? "0x0000000000000000000000000000000000000000").trim(),
    rpcUrls: (process.env.ROBINHOOD_RPC_URLS ?? process.env.ROBINHOOD_RPC_URL ?? "https://robinhood-mainnet.core.chainstack.com/f8922de06dc48d17affa815a4cde9727")
      .split(",").map((u) => u.trim()).filter(Boolean),
  },
};

for (const [name, cfg] of Object.entries(CHAIN_CONFIG)) {
  if (!isAddress(cfg.contract)) throw new Error(`${name.toUpperCase()} SETTLEMENT_CONTRACT is not a valid address: ${cfg.contract}`);
  // Robinhood contract is a placeholder zero address until deployed — skip validation.
  if (name !== "robinhood" && cfg.contract === "0x0000000000000000000000000000000000000000") {
    throw new Error(`${name.toUpperCase()} SETTLEMENT_CONTRACT is not configured`);
  }
}

// ── Solana configuration ──────────────────────────────────────────────────────

const SOLANA_RPC_URLS = (
  process.env.SOLANA_RPC_URLS ?? process.env.SOLANA_RPC_URL ?? "https://api.mainnet-beta.solana.com"
).split(",").map((u) => u.trim()).filter(Boolean);
const SOLANA_RPC_TIMEOUT_MS = Math.max(1000, Number(process.env.SOLANA_RPC_TIMEOUT_MS ?? 12000));
const solanaRpcCooldownUntil = new Map();
let solanaRpcCursor = 0;

const SOLANA_EXECUTOR_PRIVATE_KEY = resolveUniqueConfigValue([
  process.env.SOLANA_EXECUTOR_PRIVATE_KEY,
  process.env.DEVNET_EXECUTOR_PRIVATE_KEY,
], "Solana executor private key");
const SOLANA_EXECUTOR_PUBLIC_KEY = resolveUniqueConfigValue([
  process.env.SOLANA_EXECUTOR_PUBLIC_KEY,
  process.env.DEVNET_EXECUTOR_PUBLIC_KEY,
  process.env.VITE_SOLANA_EXECUTOR_ADDRESS,
], "Solana executor public key");
const ALLOW_LEGACY_SOLANA_SIGNATURES = process.env.SOLANA_ALLOW_LEGACY_SIGNATURES === "true";
const ALLOW_MAINNET_LIVE = process.env.ALLOW_MAINNET_LIVE === "true";

if (process.env.SETTLEMENT_LIVE === "true" && SOLANA_RPC_URLS.some((url) => /mainnet-beta/i.test(url)) && !ALLOW_MAINNET_LIVE) {
  throw new Error("Refusing live settlement: mainnet Solana RPC configured while SETTLEMENT_LIVE=true. Set ALLOW_MAINNET_LIVE=true to allow this explicit live-mainnet test.");
}

// Build Solana keypair from base58 private key (if configured)
let solanaKeypair = null;
if (SOLANA_EXECUTOR_PRIVATE_KEY) {
  try {
    const decoded = bs58.decode(SOLANA_EXECUTOR_PRIVATE_KEY);
    solanaKeypair = Keypair.fromSecretKey(decoded);
    if (SOLANA_EXECUTOR_PUBLIC_KEY && solanaKeypair.publicKey.toBase58() !== SOLANA_EXECUTOR_PUBLIC_KEY.trim()) {
      throw new Error(`private key derives ${solanaKeypair.publicKey.toBase58()}, expected ${SOLANA_EXECUTOR_PUBLIC_KEY.trim()}`);
    }
    console.log(`[solana] Executor: ${solanaKeypair.publicKey.toString()}`);
  } catch (err) {
    throw new Error(`[solana] Invalid executor configuration: ${err.message}`);
  }
}

class HttpOnlySolanaConnection extends Connection {
  async confirmTransaction(strategy, commitment = "confirmed") {
    const signature = typeof strategy === "string" ? strategy : strategy.signature;
    const lastValidBlockHeight = typeof strategy === "object" && "lastValidBlockHeight" in strategy
      ? strategy.lastValidBlockHeight
      : undefined;
    const deadline = Date.now() + 90_000;
    while (Date.now() < deadline) {
      const status = (await this.getSignatureStatuses([signature], { searchTransactionHistory: true })).value[0];
      if (status?.err) return { context: { slot: 0 }, value: { err: status.err } };
      if (status?.confirmationStatus === "confirmed" || status?.confirmationStatus === "finalized") {
        return { context: { slot: 0 }, value: { err: null } };
      }
      if (lastValidBlockHeight !== undefined && (await this.getBlockHeight(commitment)) > lastValidBlockHeight) {
        throw new Error(`Transaction ${signature} expired before confirmation`);
      }
      await new Promise((resolve) => setTimeout(resolve, 500));
    }
    throw new Error(`Timed out waiting for transaction ${signature}`);
  }
}

function solanaConnectionConfig() {
  return {
    commitment: "confirmed",
    disableRetryOnRateLimit: true,
    fetchMiddleware: (info, init, next) => {
      next(info, { ...init, signal: AbortSignal.timeout(SOLANA_RPC_TIMEOUT_MS) });
    },
  };
}

async function getSolanaConnection() {
  let lastError;
  const now = Date.now();
  const urls = SOLANA_RPC_URLS.map((_, index) => SOLANA_RPC_URLS[(solanaRpcCursor + index) % SOLANA_RPC_URLS.length]);
  solanaRpcCursor = (solanaRpcCursor + 1) % Math.max(1, SOLANA_RPC_URLS.length);
  for (const url of urls) {
    if ((solanaRpcCooldownUntil.get(url) ?? 0) > now) continue;
    const connection = new HttpOnlySolanaConnection(url, solanaConnectionConfig());
    try {
      await connection.getLatestBlockhash("confirmed");
      return createSolanaRpcRouter(connection);
    } catch (error) {
      lastError = error;
      const message = error instanceof Error ? error.message : String(error);
      const cooldown = /429|rate limit|too many requests/i.test(message) ? 30000 : 5000;
      solanaRpcCooldownUntil.set(url, Date.now() + cooldown);
      console.warn(`[solana] RPC unavailable for ${cooldown}ms: ${url} (${message})`);
    }
  }
  const retryAfter = Math.max(250, Math.min(...SOLANA_RPC_URLS.map((url) => Math.max(0, (solanaRpcCooldownUntil.get(url) ?? 0) - Date.now())).filter((value) => value > 0), 5000));
  await new Promise((resolve) => setTimeout(resolve, retryAfter));
  throw new Error(`No Solana RPC endpoint is healthy: ${lastError instanceof Error ? lastError.message : lastError}`);
}

function getSolanaConnections() {
  return SOLANA_RPC_URLS.map((url) => new HttpOnlySolanaConnection(url, solanaConnectionConfig()));
}

function isRetryableSolanaRpcError(error) {
  const message = error instanceof Error ? error.message : String(error);
  return /429|rate limit|too many requests|fetch failed|timeout|timed out|network|econnreset|502|503|504/i.test(message);
}

function createSolanaRpcRouter(primaryConnection) {
  const connections = [primaryConnection, ...getSolanaConnections().filter((connection) => connection.rpcEndpoint !== primaryConnection.rpcEndpoint)];
  let cursor = 0;
  return new Proxy(primaryConnection, {
    get(_target, property) {
      const active = connections[cursor];
      const value = active[property];
      if (typeof value !== "function") return value;
      return async (...args) => {
        let lastError;
        for (let attempt = 0; attempt < connections.length; attempt += 1) {
          const index = (cursor + attempt) % connections.length;
          const connection = connections[index];
          try {
            const result = await connection[property](...args);
            cursor = index;
            return result;
          } catch (error) {
            lastError = error;
            if (!isRetryableSolanaRpcError(error) || property === "sendRawTransaction") throw error;
            const endpoint = connection.rpcEndpoint;
            const cooldown = /429|rate limit|too many requests/i.test(String(error)) ? 30000 : 5000;
            solanaRpcCooldownUntil.set(endpoint, Date.now() + cooldown);
            console.warn(`[solana] RPC ${String(property)} failed; rotating from ${endpoint}`);
          }
        }
        throw lastError;
      };
    },
  });
}

function canonicalSolanaOrderMessage(order) {
  const message = {
    maker: order.maker,
    tokenIn: order.tokenIn,
    tokenOut: order.tokenOut,
    amountIn: order.amountIn,
    amount: order.amount,
    amountOutMin: order.amountOutMin,
    expiration: order.expiration,
    nonce: order.nonce,
    salt: order.salt,
    pairId: order.pairId,
    side: order.side,
    price: order.price,
    network: "solana",
    tokenInAccount: order.tokenInAccount,
    tokenOutAccount: order.tokenOutAccount,
  };
  const body = JSON.stringify(message, Object.keys(message).sort());
  return new TextEncoder().encode(`Aster DEX Order:\n${body}`);
}

function decodeSolanaSignature(signature) {
  const value = String(signature ?? "").trim();
  if (/^[A-Za-z0-9+/]+={0,2}$/.test(value) && value.length % 4 === 0) {
    const decoded = Buffer.from(value, "base64");
    if (decoded.length === 64) return new Uint8Array(decoded);
  }
  const decoded = bs58.decode(value);
  if (decoded.length !== 64) throw new Error("Solana signature must decode to 64 bytes");
  return decoded;
}

async function verifySolanaOrder(order) {
  const maker = new PublicKey(order.maker);
  const tokenInAccount = order.tokenInAccount ?? await getATAAddress(order.maker, order.tokenIn);
  const tokenOutAccount = order.tokenOutAccount ?? await getATAAddress(order.maker, order.tokenOut);

  // Ladder children are generated server-side from a parent order that was
  // signature-verified at creation. Their price/amount fields intentionally
  // differ from the parent signature, so verify the parent at ingress and
  // trust only the persisted child relationship here.
  const isVerifiedServerChild = Boolean(order.isLadder && order.ladderParentHash);
  try {
    if (isVerifiedServerChild) {
      if (!order.ladderParentHash) throw new Error("Missing ladder parent hash");
    } else {
      const signature = decodeSolanaSignature(order.signature);
      const valid = nacl.sign.detached.verify(
        canonicalSolanaOrderMessage({ ...order, tokenInAccount, tokenOutAccount }),
        signature,
        maker.toBytes(),
      );
      if (!valid) {
        if (!ALLOW_LEGACY_SOLANA_SIGNATURES) throw new Error("Solana order signature mismatch");
        console.warn(`[solana] legacy signature mismatch for ${order.orderHash}; continuing because SOLANA_ALLOW_LEGACY_SIGNATURES=true`);
      }
    }
  } catch (error) {
    if (!ALLOW_LEGACY_SOLANA_SIGNATURES) throw error;
    console.warn(`[solana] legacy signature verification failed for ${order.orderHash}; continuing because SOLANA_ALLOW_LEGACY_SIGNATURES=true (${error.message})`);
  }

  if (Number(order.expiration) <= Math.floor(Date.now() / 1000)) {
    throw new Error(`Expired Solana order ${order.orderHash}`);
  }
}

/**
 * Settle a matched Solana fill by transferring tokens directly between
 * the two users' token accounts using the executor's SPL delegate authority.
 *
 * Safety checks (in order):
 *   1. Both makers must have authorized the executor as SPL delegate
 *   2. Both makers must have sufficient token balance right now
 *   3. Both transfer transactions must pass simulation
 *   4. Execute sell-side transfer first, then buy-side
 *   5. If buy-side fails after sell-side succeeds → log + retry on next cycle
 */
async function settleSolana(payload, { resumePartial = false } = {}) {
  const { fill, buyOrder, sellOrder } = payload;

  if (!LIVE) {
    console.log(`[solana] fill=${fill.id} simulation_only (SETTLEMENT_LIVE=false)`);
    return { status: "failed", txHash: "", error: "simulation_only" };
  }

  if (!solanaKeypair) {
    throw new Error("SOLANA_EXECUTOR_PRIVATE_KEY not configured for Solana settlement");
  }

  const conn = await getSolanaConnection();
  const executor = solanaKeypair;

  console.log(`[solana] fill=${fill.id} settling — sell=${sellOrder.maker} buy=${buyOrder.maker}`);

  // ── 1. Resolve token accounts ─────────────────────────────────────────────
  // Each order stores tokenInAccount and tokenOutAccount (user's ATAs)
  // set at order creation time.
  const sellMintIn   = new PublicKey(sellOrder.tokenIn);  // token seller is selling
  const buyMintIn    = new PublicKey(buyOrder.tokenIn);   // token buyer is paying

  // seller's tokenIn account → buyer's tokenOut account (what buyer receives)
  const sellerTokenInAcc  = new PublicKey(sellOrder.tokenInAccount  || await getATAAddress(sellOrder.maker, sellOrder.tokenIn));
  const buyerTokenOutAcc  = new PublicKey(buyOrder.tokenOutAccount  || await getATAAddress(buyOrder.maker, buyOrder.tokenOut));
  // buyer's tokenIn account → seller's tokenOut account (what seller receives)
  const buyerTokenInAcc   = new PublicKey(buyOrder.tokenInAccount   || await getATAAddress(buyOrder.maker, buyOrder.tokenIn));
  const sellerTokenOutAcc = new PublicKey(sellOrder.tokenOutAccount || await getATAAddress(sellOrder.maker, sellOrder.tokenOut));

  const amountBase  = BigInt(fill.amount);
  const amountQuote = BigInt(fill.amountQuote);

  await Promise.all([verifySolanaOrder(buyOrder), verifySolanaOrder(sellOrder)]);

  // ── 2. Balance check — fail fast before any transaction ───────────────────
  const buyerAccount = await getCheckedTokenAccount(conn, buyerTokenInAcc, buyOrder.maker, buyOrder.tokenIn, "buyer source");
  const sellerAccount = resumePartial
    ? null
    : await getCheckedTokenAccount(conn, sellerTokenInAcc, sellOrder.maker, sellOrder.tokenIn, "seller source");
  const buyerBalance = buyerAccount.amount;

  console.log(`[solana] fill=${fill.id} balances: ${resumePartial ? "partial-recovery" : `seller=${sellerAccount.amount} (need ${amountBase}) `}buyer=${buyerBalance} (need ${amountQuote})`);

  if (!resumePartial && sellerAccount.amount < amountBase) {
    throw new Error(
      `Insufficient seller balance: has ${sellerAccount.amount}, needs ${amountBase} ` +
      `(fill=${fill.id} seller=${sellOrder.maker})`,
    );
  }
  if (buyerBalance < amountQuote) {
    throw new Error(
      `Insufficient buyer balance: has ${buyerBalance}, needs ${amountQuote} ` +
      `(fill=${fill.id} buyer=${buyOrder.maker})`,
    );
  }

  // ── 3. Check delegate authority ───────────────────────────────────────────
  if (!resumePartial) await verifyDelegate(sellerAccount, executor.publicKey, amountBase, "seller");
  await verifyDelegate(buyerAccount, executor.publicKey, amountQuote, "buyer");

  // ── 4. Build transactions ─────────────────────────────────────────────────
  const { blockhash, lastValidBlockHeight } = await conn.getLatestBlockhash();

  // Check if destination ATAs exist, create them if needed
  const { createAssociatedTokenAccountInstruction } = await import("@solana/spl-token");
  
  const buyerTokenOutExists = await getCheckedDestination(conn, buyerTokenOutAcc, buyOrder.maker, buyOrder.tokenOut, "buyer destination");
  const sellerTokenOutExists = await getCheckedDestination(conn, sellerTokenOutAcc, sellOrder.maker, sellOrder.tokenOut, "seller destination");

  // sell-side: seller's tokenIn → buyer's tokenOut account
  const sellTx = new Transaction({ blockhash, lastValidBlockHeight, feePayer: executor.publicKey });
  
  // Create buyer's tokenOut ATA if it doesn't exist
  if (!resumePartial && !buyerTokenOutExists) {
    console.log(`[solana] fill=${fill.id} creating buyer tokenOut ATA`);
    sellTx.add(createAssociatedTokenAccountInstruction(
      executor.publicKey,           // payer
      buyerTokenOutAcc,              // ata
      new PublicKey(buyOrder.maker), // owner
      sellMintIn,                    // mint
      TOKEN_PROGRAM_ID,
    ));
  }
  
  if (!resumePartial) sellTx.add(createTransferInstruction(
    sellerTokenInAcc,   // source (seller's token account)
    buyerTokenOutAcc,   // destination (buyer receives this token)
    executor.publicKey, // authority (executor has delegate)
    amountBase,         // amount in raw units
    [],
    TOKEN_PROGRAM_ID,
  ));

  // buy-side: buyer's tokenIn → seller's tokenOut account
  const buyTx = new Transaction({ blockhash, lastValidBlockHeight, feePayer: executor.publicKey });
  
  // Create seller's tokenOut ATA if it doesn't exist
  if (!sellerTokenOutExists) {
    console.log(`[solana] fill=${fill.id} creating seller tokenOut ATA`);
    buyTx.add(createAssociatedTokenAccountInstruction(
      executor.publicKey,             // payer
      sellerTokenOutAcc,               // ata
      new PublicKey(sellOrder.maker),  // owner
      buyMintIn,                       // mint
      TOKEN_PROGRAM_ID,
    ));
  }
  
  buyTx.add(createTransferInstruction(
    buyerTokenInAcc,
    sellerTokenOutAcc,
    executor.publicKey,
    amountQuote,
    [],
    TOKEN_PROGRAM_ID,
  ));

  // ── 5. Simulate both transactions before broadcasting ─────────────────────
  console.log(`[solana] fill=${fill.id} simulating...`);

  const [simSell, simBuy] = await Promise.all([
    resumePartial ? Promise.resolve({ value: { err: null } }) : conn.simulateTransaction(sellTx, [executor]),
    conn.simulateTransaction(buyTx, [executor]),
  ]);

  if (simSell.value.err) {
    throw new Error(`sell-side simulation failed: ${JSON.stringify(simSell.value.err)}`);
  }
  if (simBuy.value.err) {
    throw new Error(`buy-side simulation failed: ${JSON.stringify(simBuy.value.err)}`);
  }

  console.log(`[solana] fill=${fill.id} simulation passed — broadcasting`);

  // ── 6. Broadcast sell-side first ──────────────────────────────────────────
  let sellSig = fill.txHashSell || "";
  if (!resumePartial) {
    sellTx.sign(executor);
    sellSig = await conn.sendRawTransaction(sellTx.serialize(), {
      skipPreflight: false,
      maxRetries: 3,
    });
    await conn.confirmTransaction(
      { signature: sellSig, blockhash, lastValidBlockHeight },
      "confirmed",
    );
    console.log(`[solana] fill=${fill.id} sell-side confirmed: ${sellSig}`);
  } else {
    const status = await conn.getSignatureStatuses([sellSig]);
    const confirmationStatus = status.value[0]?.confirmationStatus;
    if (!status.value[0] || status.value[0].err || (confirmationStatus !== "confirmed" && confirmationStatus !== "finalized")) {
      throw new Error(`Stored sell-side transaction is not confirmed: ${sellSig}`);
    }
    console.log(`[solana] fill=${fill.id} verified existing sell-side transaction: ${sellSig}`);
  }

  // ── 7. Broadcast buy-side ─────────────────────────────────────────────────
  // Refresh blockhash since some time may have passed
  const { blockhash: bh2, lastValidBlockHeight: lvbh2 } = await conn.getLatestBlockhash();
  buyTx.recentBlockhash = bh2;
  buyTx.lastValidBlockHeight = lvbh2;
  buyTx.sign(executor);

  let buySig;
  try {
    buySig = await conn.sendRawTransaction(buyTx.serialize(), {
      skipPreflight: false,
      maxRetries: 3,
    });
    await conn.confirmTransaction(
      { signature: buySig, blockhash: bh2, lastValidBlockHeight: lvbh2 },
      "confirmed",
    );
  } catch (error) {
    const partial = new Error(`Solana partial settlement: sell leg confirmed (${sellSig}), buy leg failed`);
    partial.name = "PartialSolanaSettlementError";
    partial.sellSig = sellSig;
    partial.cause = error;
    throw partial;
  }
  console.log(`[solana] fill=${fill.id} buy-side confirmed: ${buySig}`);

  // Return the sell-side sig as the primary tx hash (both are logged)
  return {
    status: "confirmed",
    txHash: sellSig,
    error: "",
    metadata: { sellSig, buySig },
  };
}

async function settleSolanaBatch(payloads) {
  if (payloads.length === 0) return "";
  if (!LIVE) return "";
  if (!solanaKeypair) throw new Error("SOLANA_EXECUTOR_PRIVATE_KEY not configured for Solana settlement");

  const conn = await getSolanaConnection();
  const executor = solanaKeypair;
  const orderAccounts = await Promise.all(payloads.map(async (payload) => {
    const { fill, buyOrder, sellOrder } = payload;
    const sellMint = new PublicKey(sellOrder.tokenIn);
    const buyMint = new PublicKey(buyOrder.tokenIn);
    const sellerTokenIn = new PublicKey(sellOrder.tokenInAccount || await getATAAddress(sellOrder.maker, sellOrder.tokenIn));
    const buyerTokenOut = new PublicKey(buyOrder.tokenOutAccount || await getATAAddress(buyOrder.maker, buyOrder.tokenOut));
    const buyerTokenIn = new PublicKey(buyOrder.tokenInAccount || await getATAAddress(buyOrder.maker, buyOrder.tokenIn));
    const sellerTokenOut = new PublicKey(sellOrder.tokenOutAccount || await getATAAddress(sellOrder.maker, sellOrder.tokenOut));
    const amountBase = BigInt(fill.amount);
    const amountQuote = BigInt(fill.amountQuote);

    await Promise.all([verifySolanaOrder(buyOrder), verifySolanaOrder(sellOrder)]);
    return {
      fill,
      buyOrder,
      sellOrder,
      sellMint,
      buyMint,
      sellerTokenIn,
      buyerTokenOut,
      buyerTokenIn,
      sellerTokenOut,
      amountBase,
      amountQuote,
    };
  }));

  const accountKeys = [...new Map(orderAccounts.flatMap((item) => [
    [item.sellerTokenIn.toBase58(), item.sellerTokenIn],
    [item.buyerTokenIn.toBase58(), item.buyerTokenIn],
    [item.buyerTokenOut.toBase58(), item.buyerTokenOut],
    [item.sellerTokenOut.toBase58(), item.sellerTokenOut],
  ])).values()];
  const accountInfos = await conn.getMultipleAccountsInfo(accountKeys);
  const accountInfoByKey = new Map(accountKeys.map((key, index) => [key.toBase58(), accountInfos[index]]));
  const prepared = orderAccounts.map((item) => {
    const sellerInfo = accountInfoByKey.get(item.sellerTokenIn.toBase58());
    const buyerInfo = accountInfoByKey.get(item.buyerTokenIn.toBase58());
    const buyerDestinationInfo = accountInfoByKey.get(item.buyerTokenOut.toBase58());
    const sellerDestinationInfo = accountInfoByKey.get(item.sellerTokenOut.toBase58());
    const sellerAccount = unpackAccount(item.sellerTokenIn, sellerInfo);
    const buyerAccount = unpackAccount(item.buyerTokenIn, buyerInfo);
    const buyerDestination = Boolean(buyerDestinationInfo);
    const sellerDestination = Boolean(sellerDestinationInfo);

    if (sellerAccount.owner.toString() !== new PublicKey(item.sellOrder.maker).toString() || sellerAccount.mint.toString() !== item.sellOrder.tokenIn) {
      throw new Error(`seller source account mismatch for fill=${item.fill.id}`);
    }
    if (buyerAccount.owner.toString() !== new PublicKey(item.buyOrder.maker).toString() || buyerAccount.mint.toString() !== item.buyOrder.tokenIn) {
      throw new Error(`buyer source account mismatch for fill=${item.fill.id}`);
    }
    if (sellerAccount.amount < item.amountBase) throw new Error(`Insufficient seller balance for fill=${item.fill.id}`);
    if (buyerAccount.amount < item.amountQuote) throw new Error(`Insufficient buyer balance for fill=${item.fill.id}`);
    verifyDelegate(sellerAccount, executor.publicKey, item.amountBase, "seller");
    verifyDelegate(buyerAccount, executor.publicKey, item.amountQuote, "buyer");
    if (buyerDestination) solanaDestinationCache.set(item.buyerTokenOut.toBase58(), Date.now());
    if (sellerDestination) solanaDestinationCache.set(item.sellerTokenOut.toBase58(), Date.now());
    return { ...item, buyerDestination, sellerDestination };
  });

  const { blockhash, lastValidBlockHeight } = await conn.getLatestBlockhash("confirmed");
  const transaction = new Transaction({ blockhash, lastValidBlockHeight, feePayer: executor.publicKey });
  const createdAccounts = new Set();
  for (const item of prepared) {
    if (!item.buyerDestination && !createdAccounts.has(item.buyerTokenOut.toBase58())) {
      transaction.add(createAssociatedTokenAccountInstruction(
        executor.publicKey,
        item.buyerTokenOut,
        new PublicKey(item.buyOrder.maker),
        item.sellMint,
        TOKEN_PROGRAM_ID,
      ));
      createdAccounts.add(item.buyerTokenOut.toBase58());
    }
    if (!item.sellerDestination && !createdAccounts.has(item.sellerTokenOut.toBase58())) {
      transaction.add(createAssociatedTokenAccountInstruction(
        executor.publicKey,
        item.sellerTokenOut,
        new PublicKey(item.sellOrder.maker),
        item.buyMint,
        TOKEN_PROGRAM_ID,
      ));
      createdAccounts.add(item.sellerTokenOut.toBase58());
    }
    transaction.add(
      createTransferInstruction(item.sellerTokenIn, item.buyerTokenOut, executor.publicKey, item.amountBase, [], TOKEN_PROGRAM_ID),
      createTransferInstruction(item.buyerTokenIn, item.sellerTokenOut, executor.publicKey, item.amountQuote, [], TOKEN_PROGRAM_ID),
    );
  }

  const simulation = await conn.simulateTransaction(transaction, [executor]);
  if (simulation.value.err) throw new Error(`Solana batch simulation failed: ${JSON.stringify(simulation.value.err)}`);
  transaction.sign(executor);
  const txHash = await conn.sendRawTransaction(transaction.serialize(), { skipPreflight: false, maxRetries: 3 });
  await conn.confirmTransaction({ signature: txHash, blockhash, lastValidBlockHeight }, "confirmed");
  console.log(`[solana-batch] fills=${payloads.map(({ fill }) => fill.id).join(",")} confirmed tx=${txHash}`);
  return txHash;
}

async function settleSolanaChunk(payloads) {
  if (payloads.length === 1) {
    await settleIndividual(payloads[0]);
    return;
  }
  const makers = payloads.flatMap(({ buyOrder, sellOrder }) => [buyOrder.maker, sellOrder.maker]);
  try {
    const txHash = await withSolanaAccountLocks(makers, () => settleSolanaBatch(payloads));
    for (const { fill } of payloads) {
      await report(fill.id, { status: "confirmed", txHash, error: "", metadata: { batchSize: payloads.length } });
      metrics.confirmed += 1;
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.warn(`[solana-batch] fills=${payloads.map(({ fill }) => fill.id).join(",")} failed: ${message}`);
    const midpoint = Math.ceil(payloads.length / 2);
    await settleSolanaChunk(payloads.slice(0, midpoint));
    await settleSolanaChunk(payloads.slice(midpoint));
  }
}

// ── Solana helpers ────────────────────────────────────────────────────────────

async function getATAAddress(walletAddress, mintAddress) {
  const wallet = new PublicKey(walletAddress);
  const mint   = new PublicKey(mintAddress);
  const ata = await getAssociatedTokenAddress(mint, wallet, false, TOKEN_PROGRAM_ID, ASSOCIATED_TOKEN_PROGRAM_ID);
  return ata.toString();
}

async function getCheckedTokenAccount(conn, tokenAccountPubkey, owner, mint, label) {
  const account = await getAccount(conn, tokenAccountPubkey);
  if (account.owner.toString() !== new PublicKey(owner).toString()) throw new Error(`${label} owner mismatch`);
  if (account.mint.toString() !== new PublicKey(mint).toString()) throw new Error(`${label} mint mismatch`);
  return account;
}

async function getCheckedDestination(conn, tokenAccountPubkey, owner, mint, label) {
  const cacheKey = tokenAccountPubkey.toBase58();
  const cachedAt = solanaDestinationCache.get(cacheKey);
  if (cachedAt && cachedAt > Date.now() - 30000) return true;
  const info = await conn.getAccountInfo(tokenAccountPubkey);
  if (!info) return false;
  await getCheckedTokenAccount(conn, tokenAccountPubkey, owner, mint, label);
  solanaDestinationCache.set(cacheKey, Date.now());
  return true;
}

async function verifyDelegate(account, executorPubkey, requiredAmount, role) {
  if (!account.delegate || account.delegate.toString() !== executorPubkey.toString()) {
    throw new Error(
      `${role} has not delegated its token account to executor. ` +
      `User must approve the executor in the DEX UI before placing orders.`,
    );
  }
  if (BigInt(account.delegatedAmount) < requiredAmount) {
    throw new Error(
      `${role} delegated amount (${account.delegatedAmount}) is less than required (${requiredAmount}). ` +
      `User must re-approve with a higher amount.`,
    );
  }
}

async function mapWithConcurrency(items, concurrency, worker) {
  const results = new Array(items.length);
  let next = 0;
  async function run() {
    while (true) {
      const index = next++;
      if (index >= items.length) return;
      results[index] = await worker(items[index], index);
    }
  }
  await Promise.all(Array.from({ length: Math.min(concurrency, items.length) }, run));
  return results;
}

async function withSolanaAccountLocks(accounts, worker) {
  const keys = [...new Set(accounts.map((account) => String(account).toLowerCase()))].sort();
  const waits = keys.map((key) => solanaAccountLocks.get(key) ?? Promise.resolve());
  let release;
  const gate = new Promise((resolve) => { release = resolve; });
  for (const key of keys) solanaAccountLocks.set(key, gate);
  await Promise.all(waits);
  try {
    return await worker();
  } finally {
    for (const key of keys) {
      if (solanaAccountLocks.get(key) === gate) solanaAccountLocks.delete(key);
    }
    release();
  }
}

// ── Per-chain viem clients (lazy) ─────────────────────────────────────────────

const chainClients = {};
function getChainClients(network) {
  if (chainClients[network]) return chainClients[network];
  const cfg = CHAIN_CONFIG[network];
  if (!cfg) throw new Error(`Unsupported settlement network: ${network}`);
  const publicClients = cfg.rpcUrls.map((url) =>
    createPublicClient({ chain: cfg.chain, transport: http(url) }),
  );
  const walletClient = LIVE
    ? createWalletClient({ account: privateKeyToAccount(privateKey), chain: cfg.chain, transport: http(cfg.rpcUrls[0]) })
    : null;
  chainClients[network] = { publicClients, walletClient, contract: cfg.contract };
  return chainClients[network];
}

// ── ABI ───────────────────────────────────────────────────────────────────────

// Tuple type strings reused across single and batch ABIs.
const ORDER_TUPLE = "(address maker,address tokenIn,address tokenOut,uint256 amountIn,uint256 amount,uint256 amountOutMin,uint256 expiration,uint256 nonce,address receiver,uint256 salt)";
const LADDER_TUPLE = "(address maker,address tokenIn,address tokenOut,uint256 totalAmount,uint256 priceStart,uint256 priceEnd,uint256 levels,uint256 expiration,uint256 nonce,uint256 salt)";

const abi = parseAbi([
  // ── Verification ──
  `function verifySignature(${ORDER_TUPLE} o, bytes signature) view returns (bool)`,

  // ── Single fill ──
  `function matchOrders(${ORDER_TUPLE} buyOrder, bytes sigBuy, ${ORDER_TUPLE} sellOrder, bytes sigSell, uint256 amountBase)`,
  `function matchOrdersAtQuote(${ORDER_TUPLE} buyOrder, bytes sigBuy, ${ORDER_TUPLE} sellOrder, bytes sigSell, uint256 amountBase, uint256 amountQuote)`,
  `function matchOrderWithLadder(${ORDER_TUPLE} buyOrder, bytes sigBuy, ${LADDER_TUPLE} sellAuth, bytes sigSell, uint256 sellLevelIndex, uint256 amountBase)`,
  `function matchLadderOrders(${LADDER_TUPLE} buyAuth, bytes sigBuy, ${LADDER_TUPLE} sellAuth, bytes sigSell, uint256 buyLevelIndex, uint256 sellLevelIndex, uint256 amountBase)`,

  // ── Batch fill — regular orders (~8.9K gas/fill vs ~79K individually) ──
  `function batchMatchOrders(${ORDER_TUPLE}[] buyOrders, bytes[] sigsBuy, ${ORDER_TUPLE}[] sellOrders, bytes[] sigsSell, uint256[] amounts)`,

  // ── Batch fill — ladder orders (~12K gas/pair vs ~95K individually) ──
  `function batchMatchLadderOrders(${LADDER_TUPLE}[] buyAuths, bytes[] sigsBuy, ${LADDER_TUPLE}[] sellAuths, bytes[] sigsSell, uint256[] buyLevelIndices, uint256[] sellLevelIndices, uint256[] amounts)`,
]);

// ── Data conversion helpers ───────────────────────────────────────────────────

const headers = {
  "content-type": "application/json",
  "x-settlement-worker": WORKER_ID,
  ...(API_KEY ? { "x-settlement-key": API_KEY } : {}),
};

const asAddress = (value) => {
  if (!isAddress(value)) throw new Error(`Invalid address in signed order: ${value}`);
  return value;
};

const asBigInt = (value, field) => {
  try { return BigInt(value); } catch { throw new Error(`Invalid ${field}: ${value}`); }
};

const toOrder = (order) => ({
  maker: asAddress(order.maker),
  tokenIn: asAddress(order.tokenIn),
  tokenOut: asAddress(order.tokenOut),
  amountIn: asBigInt(order.amountIn, "amountIn"),
  amount: asBigInt(order.amount, "amount"),
  amountOutMin: asBigInt(order.amountOutMin, "amountOutMin"),
  expiration: asBigInt(order.expiration, "expiration"),
  nonce: asBigInt(order.nonce, "nonce"),
  receiver: asAddress(order.receiver || zeroAddress),
  salt: asBigInt(order.salt, "salt"),
});

const fixedPrice = (value) => {
  // Convert decimal price string to 8-decimal fixed-point bigint.
  // "0.00040000" → 40000n  (= 0.00040000 * 1e8)
  // Must match the frontend fixedPrice() and contract calculateLevelPrice().
  const str = String(value);
  const [whole, fraction = ""] = str.split(".");
  return BigInt(`${whole}${fraction.padEnd(8, "0").slice(0, 8)}`);
};

/**
 * Build the LadderAuth struct for the contract from a stored ladder child order.
 *
 * Critical: totalAmount must be the ORIGINAL totalAmount the maker signed over —
 * i.e. the full ladder's input token amount, not a per-level amount. The backend
 * now always stores this in ladder_total_amount. We hard-fail if it's missing so
 * bugs surface immediately rather than sending a wrong hash to the contract.
 */
const toLadder = (order) => {
  // Prefer the explicitly stored ladderTotalAmount (set by backend since fix).
  // Guard against "0", empty string, and missing field.
  const raw = order.ladderTotalAmount;
  if (!raw || raw === "0" || raw === "") {
    // Fallback (pre-fix orders still in DB): reconstruct from order fields.
    // For SELL: totalAmount = amount * levels (base token per level × levels).
    // For BUY:  totalAmount = amountIn (total quote token committed).
    // This matches what OrderForm.tsx sends as ladderAmount / amountIn.
    console.warn(
      `[toLadder] fill order ${order.id} missing ladderTotalAmount — using fallback. ` +
      `side=${order.side} amount=${order.amount} levels=${order.ladderLevels} amountIn=${order.amountIn}`,
    );
    const fallback =
      order.side === "sell"
        ? BigInt(order.amount) * BigInt(order.ladderLevels)
        : asBigInt(order.amountIn, "fallback totalAmount (amountIn)");
    return _buildLadder(order, fallback);
  }
  return _buildLadder(order, asBigInt(raw, "ladderTotalAmount"));
};

function _buildLadder(order, totalAmount) {
  return {
    maker: asAddress(order.maker),
    tokenIn: asAddress(order.tokenIn),
    tokenOut: asAddress(order.tokenOut),
    totalAmount,
    priceStart: fixedPrice(order.ladderPriceStart),
    priceEnd: fixedPrice(order.ladderPriceEnd),
    levels: asBigInt(order.ladderLevels, "ladder levels"),
    expiration: asBigInt(order.expiration, "expiration"),
    nonce: asBigInt(order.nonce, "nonce"),
    salt: asBigInt(order.salt, "salt"),
  };
}

// 0-indexed level for the contract from 1-indexed backend storage.
const levelIndex = (order) => BigInt(Math.max(0, (order.ladderLevel ?? 1) - 1));

// ── API helpers ───────────────────────────────────────────────────────────────

async function api(path, options = {}) {
  const maxAttempts = 4;
  for (let attempt = 1; attempt <= maxAttempts; attempt += 1) {
    const response = await fetch(`${API_URL}${path}`, {
      ...options,
      headers: { ...headers, ...(options.headers ?? {}) },
    });
    if (response.ok) return response.json();
    const body = await response.text();
    const retryable = response.status === 429 || response.status >= 500;
    if (!retryable || attempt === maxAttempts) {
      metrics.apiErrors += 1;
      throw new Error(`${options.method ?? "GET"} ${path} failed (${response.status}): ${body}`);
    }
    const retryAfter = Number(response.headers.get("retry-after"));
    const delay = Number.isFinite(retryAfter) && retryAfter > 0
      ? retryAfter * 1000
      : Math.min(1000 * (2 ** (attempt - 1)), 10000) + Math.floor(Math.random() * 250);
    await new Promise((resolve) => setTimeout(resolve, delay));
  }
  throw new Error(`${options.method ?? "GET"} ${path} failed after retries`);
}

async function report(id, result) {
  await api(`/api/settlement/fills/${id}/result`, { method: "POST", body: JSON.stringify(result) });
}

// ── Transaction helpers ───────────────────────────────────────────────────────

class SubmittedTransactionError extends Error {
  constructor(txHash, cause) {
    super(`Transaction ${txHash} was submitted; receipt confirmation is pending: ${cause instanceof Error ? cause.message : cause}`);
    this.txHash = txHash;
  }
}

async function waitForReceiptWithFailover(txHash, publicClients) {
  let lastError;
  for (let attempt = 0; attempt < 30; attempt += 1) {
    for (const client of publicClients) {
      try {
        return await client.getTransactionReceipt({ hash: txHash });
      } catch (error) {
        lastError = error;
      }
    }
    await new Promise((resolve) => setTimeout(resolve, 2000));
  }
  throw new SubmittedTransactionError(txHash, lastError);
}

async function simulateAndWrite(publicClient, walletClient, account, contract, functionName, args) {
  const simulation = await publicClient.simulateContract({ address: contract, abi, functionName, args, account });
  console.log(`[settlement] function=${functionName} simulation=ok`);
  if (!LIVE) return null; // simulation-only mode
  const txHash = await walletClient.writeContract(simulation.request);
  return txHash;
}

// ── Fill classification ───────────────────────────────────────────────────────

/**
 * Returns the settlement function name for a fill payload:
 *  "matchOrders"          — regular buy + regular sell
 *  "matchOrderWithLadder" — regular buy + ladder sell
 *  "matchLadderOrders"    — ladder buy + ladder sell
 */
function fillType(buyOrder, sellOrder) {
  const buyLadder = !!buyOrder.isLadder;
  const sellLadder = !!sellOrder.isLadder;
  if (!buyLadder && !sellLadder) return "matchOrders";
  if (!buyLadder && sellLadder) return "matchOrderWithLadder";
  if (buyLadder && sellLadder) return "matchLadderOrders";
  throw new Error("ladder-buy vs regular-sell is not supported by the contract");
}

// ── ERC20 preflight checks ────────────────────────────────────────────────────

const ERC20_ABI = parseAbi([
  "function balanceOf(address owner) view returns (uint256)",
  "function allowance(address owner, address spender) view returns (uint256)",
]);

/**
 * Check whether both sides of an EVM fill have sufficient balance AND allowance.
 *
 * Returns:
 *   { ok: true }  — both sides are funded and approved; safe to attempt settlement
 *   { ok: false, reason: string } — skip this fill; log and retry later
 *
 * For a fill:
 *   buy side:  buyer needs  fill.amountQuote of buyOrder.tokenIn approved to contract
 *   sell side: seller needs fill.amount       of sellOrder.tokenIn approved to contract
 */
async function evmPreflightCheck(payload, network) {
  const { fill, buyOrder, sellOrder } = payload;
  const { publicClients, contract } = getChainClients(network);
  const publicClient = publicClients[0];

  const buyerAddress  = asAddress(buyOrder.maker);
  const sellerAddress = asAddress(sellOrder.maker);
  const buyTokenIn    = asAddress(buyOrder.tokenIn);
  const sellTokenIn   = asAddress(sellOrder.tokenIn);

  // Amounts needed
  const needQuote = asBigInt(fill.amountQuote || "0", "fill.amountQuote");
  const needBase  = asBigInt(fill.amount,              "fill.amount");

  // If amountQuote is missing (old fill), fall back to buyOrder.amountIn
  const buyerNeed  = needQuote > 0n ? needQuote : asBigInt(buyOrder.amountIn, "buyOrder.amountIn");
  const sellerNeed = needBase;

  try {
    // Run all four reads in parallel — single round-trip cost
    const [buyBalance, buyAllowance, sellBalance, sellAllowance] = await Promise.all([
      publicClient.readContract({ address: buyTokenIn,  abi: ERC20_ABI, functionName: "balanceOf",  args: [buyerAddress]           }),
      publicClient.readContract({ address: buyTokenIn,  abi: ERC20_ABI, functionName: "allowance",  args: [buyerAddress, contract]  }),
      publicClient.readContract({ address: sellTokenIn, abi: ERC20_ABI, functionName: "balanceOf",  args: [sellerAddress]           }),
      publicClient.readContract({ address: sellTokenIn, abi: ERC20_ABI, functionName: "allowance",  args: [sellerAddress, contract] }),
    ]);

    if (buyBalance < buyerNeed) {
      return { ok: false, reason: `buyer insufficient balance: has ${buyBalance} needs ${buyerNeed} of ${buyTokenIn}` };
    }
    if (buyAllowance < buyerNeed) {
      return { ok: false, reason: `buyer insufficient allowance: has ${buyAllowance} needs ${buyerNeed} of ${buyTokenIn}` };
    }
    if (sellBalance < sellerNeed) {
      return { ok: false, reason: `seller insufficient balance: has ${sellBalance} needs ${sellerNeed} of ${sellTokenIn}` };
    }
    if (sellAllowance < sellerNeed) {
      return { ok: false, reason: `seller insufficient allowance: has ${sellAllowance} needs ${sellerNeed} of ${sellTokenIn}` };
    }

    return { ok: true };
  } catch (err) {
    // RPC error — don't skip the fill, let it proceed and fail at simulation
    const msg = err instanceof Error ? err.message : String(err);
    console.warn(`[preflight] fill=${fill.id} RPC error during preflight (will attempt settlement anyway): ${msg}`);
    return { ok: true };
  }
}

// ── Single-fill settlement ────────────────────────────────────────────────────

async function settleSingle(payload) {
  const { fill, buyOrder, sellOrder } = payload;
  const network = (buyOrder.network || sellOrder.network || "bsc").toLowerCase();
  const { publicClients, walletClient, contract } = getChainClients(network);
  const publicClient = publicClients[0];
  const account = privateKey ? privateKeyToAccount(privateKey) : simulatorAddress;

  let amountBase = asBigInt(fill.amount, "fill amount");
  const fType = fillType(buyOrder, sellOrder);

  let functionName;
  let args;
  if (fType === "matchOrders") {
    const usesBookQuote = buyOrder.orderType === "market" || sellOrder.orderType === "market";
    functionName = usesBookQuote ? "matchOrdersAtQuote" : "matchOrders";
    args = [toOrder(buyOrder), buyOrder.signature, toOrder(sellOrder), sellOrder.signature, amountBase];
    if (usesBookQuote) {
      const quote = asBigInt(fill.amountQuote, "fill amountQuote");
      if (quote === 0n) {
        throw new Error(`Market-order fill ${fill.id} has zero quote; backend must compute a reference-price quote before settlement`);
      }
      args.push(quote);
    }
    // Pre-verify both signatures to give a clear error before wasting gas.
    const buyOk = await publicClient.readContract({ address: contract, abi, functionName: "verifySignature", args: [toOrder(buyOrder), buyOrder.signature] });
    if (!buyOk) throw new Error(`BadSignature: buy order ${buyOrder.orderHash}`);
    const sellOk = await publicClient.readContract({ address: contract, abi, functionName: "verifySignature", args: [toOrder(sellOrder), sellOrder.signature] });
    if (!sellOk) throw new Error(`BadSignature: sell order ${sellOrder.orderHash}`);
  } else if (fType === "matchOrderWithLadder") {
    functionName = "matchOrderWithLadder";
    const sellLevel = levelIndex(sellOrder);
    // ── amountBase affordability guard for matchOrderWithLadder ─────────────
    // The contract re-derives amountQuote from the ladder price at sellLevelIndex.
    // If the buy order's amountIn is insufficient for that quote, the contract
    // reverts PriceTooLow.
    //
    // The backend already computed the correct proportional quote for this
    // specific fill and stored it as fill.amountQuote. Use that directly to
    // cap amountBase — this correctly handles partial fills and the case where
    // a prior fill against another ladder level already consumed part of the
    // buyer's budget (which is the root cause of the SafeERC20 revert when
    // two fills for the same buy order are settled against different levels).
    //
    // Formula: maxBase = floor(fill.amountQuote * sellAmount / sellAmountOutMin)
    // This inverts the contract's _quoteAmountFromBase so that the resulting
    // quote == fill.amountQuote (within integer rounding).
    const fillAmountQuote    = asBigInt(fill.amountQuote,      "fill.amountQuote");
    const sellAmountOutMin   = asBigInt(sellOrder.amountOutMin, "sellOrder.amountOutMin");
    const sellAmount         = asBigInt(sellOrder.amount,       "sellOrder.amount");
    const buyAmountIn        = asBigInt(buyOrder.amountIn,      "buyOrder.amountIn");

    // Prefer capping via fill.amountQuote (precise per-fill budget).
    // Fall back to full buyAmountIn only when amountQuote is unavailable (legacy fills).
    const effectiveBudget = fillAmountQuote > 0n ? fillAmountQuote : buyAmountIn;

    if (sellAmountOutMin > 0n && sellAmount > 0n && effectiveBudget > 0n) {
      // maxBase = floor(effectiveBudget * sellAmount / sellAmountOutMin)
      const maxBase = (effectiveBudget * sellAmount) / sellAmountOutMin;
      if (maxBase < amountBase) {
        console.log(
          `[settlement] fill=${fill.id} amountBase capped ${amountBase}→${maxBase} ` +
          `(fill.amountQuote=${fillAmountQuote} sell.amountOutMin=${sellAmountOutMin} sell.amount=${sellAmount})`,
        );
        amountBase = maxBase;
      }
    }

    if (amountBase <= 0n) {
      throw new Error(`matchOrderWithLadder: buy amountIn (${buyOrder.amountIn}) cannot afford any fill at sell level price`);
    }

    args = [toOrder(buyOrder), buyOrder.signature, toLadder(sellOrder), sellOrder.signature, sellLevel, amountBase];
    const buyOk = await publicClient.readContract({ address: contract, abi, functionName: "verifySignature", args: [toOrder(buyOrder), buyOrder.signature] });
    if (!buyOk) throw new Error(`BadSignature: buy order ${buyOrder.orderHash}`);
  } else {
    functionName = "matchLadderOrders";
    args = [toLadder(buyOrder), buyOrder.signature, toLadder(sellOrder), sellOrder.signature, levelIndex(buyOrder), levelIndex(sellOrder), amountBase];
  }

  console.log(`[settlement] fill=${fill.id} network=${network} function=${functionName}`);

  // ── In-line preflight (second gate) before broadcasting ──────────────────
  // Guards against race conditions where balance/allowance dropped between
  // the pre-claim preflight and now (e.g. user revoked approval mid-flight).
  if (network !== "solana") {
    const pre = await evmPreflightCheck(payload, network);
    if (!pre.ok) {
      // Don't count this as a hard failure — log it and let the caller
      // report it as "failed" so the fill retries on the next cycle.
      throw new Error(`preflight failed before broadcast: ${pre.reason}`);
    }
  }

  const txHash = await simulateAndWrite(publicClient, walletClient, account, contract, functionName, args);
  if (txHash === null) return { status: "failed", txHash: "", error: "simulation_only" };
  const receipt = await waitForReceiptWithFailover(txHash, publicClients);
  if (receipt.status !== "success") return { status: "failed", txHash, error: "transaction_reverted" };
  return { status: "confirmed", txHash, error: "" };
}

// ── Batch settlement ──────────────────────────────────────────────────────────

/**
 * Attempt to settle an array of payloads in one batch transaction.
 * All payloads must be on the same network and of the same fill type.
 *
 * Returns: { settled: string[], failed: {id, error}[] }
 *   settled — fill IDs successfully confirmed in the batch tx
 *   failed  — fill IDs that need individual retry (simulation failed, etc.)
 */
async function settleBatch(payloads, network) {
  if (payloads.length === 0) return { settled: [], failed: [] };

  // ── Preflight all fills in the batch ────────────────────────────────────────
  // Any fill that fails the balance/allowance check is pulled out and returned
  // as "failed" (will retry individually on the next poll cycle). The remaining
  // fills are still batched together.
  const preflightResults = await Promise.all(
    payloads.map(async (payload) => {
      const result = await evmPreflightCheck(payload, network);
      return { payload, ...result };
    }),
  );
  const passedPayloads = preflightResults.filter((r) => r.ok).map((r) => r.payload);
  const failedByPreflight = preflightResults
    .filter((r) => !r.ok)
    .map((r) => ({ id: r.payload.fill.id, error: `preflight_failed: ${r.reason}` }));

  if (failedByPreflight.length > 0) {
    console.log(`[preflight-batch] fill(s) dropped before batch: ${failedByPreflight.map((f) => `${f.id}(${f.error})`).join(", ")}`);
  }
  if (passedPayloads.length === 0) {
    return { settled: [], failed: failedByPreflight };
  }

  const { publicClients, walletClient, contract } = getChainClients(network);
  const publicClient = publicClients[0];
  const account = privateKey ? privateKeyToAccount(privateKey) : simulatorAddress;

  // Determine batch function from first payload (all should be same type).
  const { buyOrder: b0, sellOrder: s0 } = passedPayloads[0];
  const fType = fillType(b0, s0);

  let functionName;
  let args;

  if (fType === "matchOrders") {
    functionName = "batchMatchOrders";
    args = [
      passedPayloads.map((p) => toOrder(p.buyOrder)),
      passedPayloads.map((p) => p.buyOrder.signature),
      passedPayloads.map((p) => toOrder(p.sellOrder)),
      passedPayloads.map((p) => p.sellOrder.signature),
      passedPayloads.map((p) => asBigInt(p.fill.amount, "fill amount")),
    ];
  } else if (fType === "matchOrderWithLadder") {
    // matchOrderWithLadder is NOT a batch function in the contract — fall through
    // to individual settlement for each.
    return { settled: [], failed: [...failedByPreflight, ...passedPayloads.map((p) => ({ id: p.fill.id, error: "no_batch_for_matchOrderWithLadder" }))] };
  } else {
    // matchLadderOrders → batchMatchLadderOrders
    functionName = "batchMatchLadderOrders";
    args = [
      passedPayloads.map((p) => toLadder(p.buyOrder)),
      passedPayloads.map((p) => p.buyOrder.signature),
      passedPayloads.map((p) => toLadder(p.sellOrder)),
      passedPayloads.map((p) => p.sellOrder.signature),
      passedPayloads.map((p) => levelIndex(p.buyOrder)),
      passedPayloads.map((p) => levelIndex(p.sellOrder)),
      passedPayloads.map((p) => asBigInt(p.fill.amount, "fill amount")),
    ];
  }

  const fillIds = passedPayloads.map((p) => p.fill.id);
  console.log(`[batch] network=${network} function=${functionName} fills=[${fillIds.join(",")}]`);

  try {
    const txHash = await simulateAndWrite(publicClient, walletClient, account, contract, functionName, args);
    if (txHash === null) {
      // simulation_only — report all as failed so they don't pile up
      return {
        settled: [],
        failed: [...failedByPreflight, ...passedPayloads.map((p) => ({ id: p.fill.id, error: "simulation_only" }))],
      };
    }
    const receipt = await waitForReceiptWithFailover(txHash, publicClients);
    if (receipt.status !== "success") {
      console.warn(`[batch] tx ${txHash} reverted — will retry individually`);
      return {
        settled: [],
        failed: [...failedByPreflight, ...passedPayloads.map((p) => ({ id: p.fill.id, error: "batch_tx_reverted" }))],
      };
    }
    console.log(`[batch] confirmed txHash=${txHash} settled ${fillIds.length} fills`);
    return { settled: fillIds, failed: failedByPreflight, txHash };
  } catch (err) {
    const message = err instanceof Error ? err.message : String(err);
    console.warn(`[batch] simulation/submission failed: ${message} — will retry individually`);
    return {
      settled: [],
      failed: [...failedByPreflight, ...passedPayloads.map((p) => ({ id: p.fill.id, error: `batch_failed: ${message}` }))],
    };
  }
}

// ── Retry / backoff ───────────────────────────────────────────────────────────

const MAX_SETTLEMENT_ATTEMPTS = 5;

function backoffMs(attempts) {
  if (attempts <= 1) return 0;
  return Math.min(5000 * (2 ** (attempts - 2)), 5 * 60 * 1000);
}

function isReadyForRetry(fill) {
  if (fill.settlementAttempts >= MAX_SETTLEMENT_ATTEMPTS) return false;
  if (fill.settlementAttempts > 0 && fill.lastAttemptedAt) {
    const elapsed = Date.now() - new Date(fill.lastAttemptedAt).getTime();
    if (elapsed < backoffMs(fill.settlementAttempts)) return false;
  }
  return true;
}

// ── Main poll loop ────────────────────────────────────────────────────────────

async function processOnce() {
  metrics.polls += 1;
  const pending = await api(`/api/settlement/pending?limit=${POLL_LIMIT}${SETTLEMENT_NETWORK ? `&network=${encodeURIComponent(SETTLEMENT_NETWORK)}` : ""}${SETTLEMENT_PAIR_ID ? `&pairId=${encodeURIComponent(SETTLEMENT_PAIR_ID)}` : ""}`);

  // ── Step 1: Handle in-flight (processing) fills first ──────────────────────
  const recovering = pending.filter((c) => c.fill.settlementStatus === "processing");
  await mapWithConcurrency(recovering, SOLANA_CONCURRENCY, async ({ fill }) => {
    try {
      if (fill.txHash || fill.txHashSell) {
        const recoveryPayload = await api(`/api/settlement/fills/${fill.id}/claim`, { method: "POST" }).catch(() => null);
        if (!recoveryPayload) return;
        const network = (recoveryPayload.buyOrder?.network || recoveryPayload.sellOrder?.network || fill.network || "bsc").toLowerCase();
        if (network === "solana" && recoveryPayload.fill.txHashSell && !recoveryPayload.fill.txHashBuy) {
          await settleIndividual(recoveryPayload);
          return;
        }
        const { publicClients } = getChainClients(network);
        const receipt = await waitForReceiptWithFailover(fill.txHash || fill.txHashSell, publicClients);
        await report(fill.id, {
          status: receipt.status === "success" ? "confirmed" : "failed",
          txHash: fill.txHash,
          error: receipt.status === "success" ? "" : "transaction_reverted",
        });
      } else {
        await report(fill.id, { status: "failed", txHash: "", error: "processing_stale_no_txhash" }).catch(() => {});
      }
    } catch (err) {
      console.error(`[settlement] recovery fill=${fill.id} failed: ${err instanceof Error ? err.message : err}`);
    }
  });

  // ── Step 2: Collect actionable pending fills ────────────────────────────────
  const actionable = pending.filter((c) => {
    const { fill } = c;
    if (fill.settlementStatus === "processing") return false; // handled above
    if (!isReadyForRetry(fill)) {
      if (fill.settlementAttempts >= MAX_SETTLEMENT_ATTEMPTS) {
        console.warn(`[settlement] fill=${fill.id} permanently abandoned after ${fill.settlementAttempts} attempts`);
      }
      return false;
    }
    return true;
  });

  if (actionable.length === 0) return;

  // ── Step 2b: EVM preflight — check balance + allowance before claiming ──────
  // Filters out fills where either counterparty lacks funds or approval.
  // We check BEFORE claiming so we don't consume an attempt slot on a fill
  // that will definitely revert. Skipped fills remain "pending" and will be
  // retried on the next poll cycle (up to MAX_SETTLEMENT_ATTEMPTS times, with
  // the order expiry swept automatically by the pending query above).
  //
  // Solana fills skip this — the settleSolana() function already does its own
  // balance + delegate checks before broadcasting.
  const preflightPassed = await mapWithConcurrency(actionable, SOLANA_CONCURRENCY, async (item) => {
    const { fill } = item;
    const network = (fill.network || "bsc").toLowerCase();
    if (network === "solana") return item; // handled inside settleSolana

    // The pending endpoint already returns full buyOrder/sellOrder — use them.
    const { buyOrder, sellOrder } = item;
    if (!buyOrder || !sellOrder) return item; // missing data, let claim decide

    const result = await evmPreflightCheck(item, network);
    if (!result.ok) {
      console.log(`[preflight] fill=${fill.id} skipped — ${result.reason}`);
      return null; // drop from this batch; it will reappear in the next poll
    }
    return item;
  });

  const actionableAfterPreflight = preflightPassed.filter(Boolean);
  if (actionableAfterPreflight.length === 0) return;

  // ── Step 3: Claim all actionable fills ─────────────────────────────────────
  // Claim atomically so no other executor instance picks them up.
  const claimedResults = await mapWithConcurrency(actionableAfterPreflight, SOLANA_CONCURRENCY, async ({ fill }) => {
    try {
      return await api(`/api/settlement/fills/${fill.id}/claim`, { method: "POST" });
    } catch (err) {
      console.warn(`[settlement] claim fill=${fill.id} failed: ${err instanceof Error ? err.message : err}`);
      return null;
    }
  });
  const claimed = claimedResults.filter(Boolean);
  metrics.claimed += claimed.length;

  if (claimed.length === 0) return;

  // ── Step 4: Group by network + fill type for batching ──────────────────────
  // Groups: `${network}:${fillType}` → payload[]
  const groups = new Map();
  const solanaPayloads = [];
  const ungroupable = []; // fills that can't be batched (matchOrderWithLadder)

  for (const payload of claimed) {
    const { buyOrder, sellOrder } = payload;
    const network = (buyOrder.network || sellOrder.network || "bsc").toLowerCase();

    // Solana fills use atomic transfer micro-batches.
    if (network === "solana") {
      solanaPayloads.push(payload);
      continue;
    }

    let fType;
    try {
      fType = fillType(buyOrder, sellOrder);
    } catch (err) {
      ungroupable.push({ payload, error: err instanceof Error ? err.message : String(err) });
      continue;
    }

    // matchOrderWithLadder has no batch variant — settle individually
    if (fType === "matchOrderWithLadder" || buyOrder.orderType === "market" || sellOrder.orderType === "market") {
      ungroupable.push({ payload, error: null });
      continue;
    }

    const key = `${network}:${fType}`;
    if (!groups.has(key)) groups.set(key, { network, fType, payloads: [] });
    groups.get(key).payloads.push(payload);
  }

  // ── Step 5: Settle Solana fills in micro-batches ────────────────────────────
  const solanaChunks = [];
  for (let i = 0; i < solanaPayloads.length; i += SOLANA_BATCH_SIZE) {
    solanaChunks.push(solanaPayloads.slice(i, i + SOLANA_BATCH_SIZE));
  }
  await mapWithConcurrency(solanaChunks, SOLANA_CONCURRENCY, settleSolanaChunk);

  // ── Step 6: Settle each EVM group in batches ────────────────────────────────
  for (const { network, payloads } of groups.values()) {
    // Split into BATCH_SIZE chunks
    for (let i = 0; i < payloads.length; i += BATCH_SIZE) {
      const chunk = payloads.slice(i, i + BATCH_SIZE);

      if (chunk.length === 1) {
        // Single fill — use individual settlement (no batch overhead)
        const payload = chunk[0];
        await settleIndividual(payload);
        continue;
      }

      // Multi-fill batch attempt
      const { settled, failed, txHash } = await settleBatch(chunk, network);

      // Report successes
      for (const id of settled) {
        try {
          await report(id, { status: "confirmed", txHash, error: "" });
        } catch (err) {
          console.error(`[batch] report fill=${id} failed: ${err instanceof Error ? err.message : err}`);
        }
      }

      // Fall back to individual for any that failed in batch
      for (const { id, error } of failed) {
        const payload = chunk.find((p) => p.fill.id === id);
        if (!payload) continue;
        console.log(`[settlement] fill=${id} retrying individually (batch reason: ${error})`);
        await settleIndividual(payload);
      }
    }
  }

  // ── Step 7: Settle ungroupable fills individually ──────────────────────────
  // matchOrderWithLadder fills that share the same buy order must be settled
  // SEQUENTIALLY — concurrent settlement causes both to pass simulation while
  // the buyer still has tokens, then the second one reverts on-chain with
  // SafeERC20: transferFrom failed because the first fill already drained
  // the buyer's allowance.
  //
  // Group by buy order hash first; within each group settle in price order
  // (lowest ladder level first). Independent buy orders can still run in
  // parallel across groups.
  const ungroupableByBuyOrder = new Map();
  for (const item of ungroupable) {
    const key = item.payload?.buyOrder?.orderHash ?? "unknown";
    if (!ungroupableByBuyOrder.has(key)) ungroupableByBuyOrder.set(key, []);
    ungroupableByBuyOrder.get(key).push(item);
  }

  // Sort each group by sell ladder level (ascending) so the cheapest level
  // is settled first — matches the order the contract expects.
  for (const group of ungroupableByBuyOrder.values()) {
    group.sort((a, b) => {
      const la = a.payload?.sellOrder?.ladderLevel ?? 0;
      const lb = b.payload?.sellOrder?.ladderLevel ?? 0;
      return la - lb;
    });
  }

  await mapWithConcurrency([...ungroupableByBuyOrder.values()], SOLANA_CONCURRENCY, async (group) => {
    // Settle fills for the same buy order one-by-one
    for (const { payload, error } of group) {
      if (error) {
        // Invalid fill type — permanently fail it
        try { await report(payload.fill.id, { status: "failed", txHash: "", error }); } catch {}
        continue;
      }
      await settleIndividual(payload);
    }
  });
}

// Wraps settleSingle / settleSolana with error handling and reporting.
async function settleIndividual(payload) {
  const { fill, buyOrder, sellOrder } = payload;
  const network = (buyOrder.network || sellOrder.network || "bsc").toLowerCase();
  try {
    // Route Solana fills to the dedicated Solana settler
    const result = network === "solana"
      ? await withSolanaAccountLocks(
          [buyOrder.maker, sellOrder.maker],
          () => settleSolana(payload, { resumePartial: Boolean(fill.txHashSell && !fill.txHashBuy) }),
        )
      : await settleSingle(payload);
    await report(fill.id, result);
    if (result.status === "confirmed") metrics.confirmed += 1;
    else if (result.status === "partial") metrics.partial += 1;
    else metrics.failed += 1;
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.error(`[settlement] fill=${fill.id} failed: ${message}`);
    metrics.failed += 1;
    if (fill.settlementAttempts > 0) metrics.retries += 1;
    try {
      if (error instanceof SubmittedTransactionError) {
        await report(fill.id, { status: "submitted", txHash: error.txHash, error: message });
      } else if (error?.name === "PartialSolanaSettlementError") {
        await report(fill.id, {
          status: "partial",
          txHash: error.sellSig,
          error: message,
          metadata: { sellSig: error.sellSig },
        });
      } else {
        await report(fill.id, { status: "failed", txHash: "", error: message });
      }
    } catch (reportError) {
      console.error(`[settlement] fill=${fill.id} report failed: ${reportError}`);
    }
  }
}

setInterval(() => {
  const elapsedSeconds = Math.max(1, (Date.now() - metrics.startedAt) / 1000);
  console.log(`[metrics] worker=${WORKER_ID} polls=${metrics.polls} claimed=${metrics.claimed} confirmed=${metrics.confirmed} failed=${metrics.failed} partial=${metrics.partial} retries=${metrics.retries} apiErrors=${metrics.apiErrors} throughput=${(metrics.confirmed / elapsedSeconds).toFixed(2)}/s`);
}, 60000).unref();

// ── Entry point ───────────────────────────────────────────────────────────────

if (ONCE) {
  await processOnce();
} else {
  for (;;) {
    try {
      await processOnce();
    } catch (err) {
      // Top-level errors (e.g. API down) should not crash the executor.
      console.error(`[executor] poll error: ${err instanceof Error ? err.message : err}`);
    }
    await new Promise((resolve) => setTimeout(resolve, INTERVAL_MS));
  }
}
