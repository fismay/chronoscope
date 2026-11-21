# Chronoscope — статичный веб-прибор, отдаётся nginx'ом
FROM nginx:alpine

COPY index.html app.js /usr/share/nginx/html/

EXPOSE 80

HEALTHCHECK --interval=30s --timeout=3s CMD wget -qO- http://localhost/ >/dev/null || exit 1
