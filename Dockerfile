FROM node:22-bookworm-slim

WORKDIR /app
COPY package.json ./
RUN npm install --omit=dev --no-audit --no-fund
COPY settlement-executor.mjs ./

CMD ["node", "settlement-executor.mjs"]