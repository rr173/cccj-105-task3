FROM node:20-alpine

WORKDIR /app
COPY package.json ./
COPY shared ./shared
COPY server ./server
COPY public ./public

ENV PORT=8080 DATA_DIR=/app/data
RUN mkdir -p /app/data && chown -R node:node /app
VOLUME ["/app/data"]
EXPOSE 8080

USER node
CMD ["node", "server/server.js"]
