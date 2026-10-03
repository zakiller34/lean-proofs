// Service Worker Predi : coquille applicative disponible hors ligne.
// Les données météo ne sont pas mises en cache ici : l'app conserve la dernière prévision elle-même.

const VERSION = 'predi-v1';

const SHELL = [
  './',
  './index.html',
  './manifest.json',
  './icons/icon.svg',
  './icons/icon-192.png',
  './icons/icon-512.png',
  './icons/icon-maskable-512.png',
  './src/styles/main.css',
  './src/main.js',
  './src/config.js',
  './src/api/openMeteo.js',
  './src/components/CurrentWeather.js',
  './src/components/ForecastList.js',
  './src/components/WeatherIcon.js',
  './src/utils/format.js',
  './src/utils/sun.js',
  './src/utils/time.js',
  './src/utils/wmo.js',
];

self.addEventListener('install', (event) => {
  event.waitUntil(
    caches
      .open(VERSION)
      .then((cache) => cache.addAll(SHELL))
      .then(() => self.skipWaiting()),
  );
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches
      .keys()
      .then((keys) => Promise.all(keys.filter((k) => k !== VERSION).map((k) => caches.delete(k))))
      .then(() => self.clients.claim()),
  );
});

// Stale-while-revalidate pour les fichiers de l'app ; le reste (API) passe directement au réseau.
self.addEventListener('fetch', (event) => {
  const { request } = event;
  if (request.method !== 'GET' || new URL(request.url).origin !== self.location.origin) return;

  event.respondWith(
    caches.open(VERSION).then(async (cache) => {
      const cached = await cache.match(request, { ignoreSearch: true });
      const network = fetch(request)
        .then((res) => {
          if (res.ok) cache.put(request, res.clone());
          return res;
        })
        .catch(() => null);

      if (cached) {
        event.waitUntil(network);
        return cached;
      }
      const res = await network;
      if (res) return res;
      if (request.mode === 'navigate') return cache.match('./index.html');
      return Response.error();
    }),
  );
});
