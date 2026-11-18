/* IV Lab service worker: makes the installed app open and work offline.
   - App files: served from cache, refreshed in the background (bump VERSION after editing the site).
   - OCR engine + language data and Pokémon sprites: cached the first time they are used. */
const VERSION = 'ivlab-2026-11-18c';
const SHELL = [
  './', './index.html', './style.css', './app.js', './import.js', './data/data.js', './manifest.webmanifest',
  './icons/icon-192.png', './icons/icon-512.png', './icons/apple-touch-icon.png', './icons/favicon-32.png',
];
const RUNTIME = 'ivlab-runtime-v1';   // big, rarely-changing files (OCR, sprites, fonts) survive app updates

self.addEventListener('install', e => {
  e.waitUntil(caches.open(VERSION).then(c => c.addAll(SHELL)).then(() => self.skipWaiting()));
});
self.addEventListener('activate', e => {
  e.waitUntil((async () => {
    for (const k of await caches.keys()) if (k !== VERSION && k !== RUNTIME) await caches.delete(k);
    await self.clients.claim();
  })());
});

const isRuntime = url =>
  url.pathname.includes('/vendor/') ||
  url.hostname === 'raw.githubusercontent.com' ||
  url.hostname === 'fonts.googleapis.com' || url.hostname === 'fonts.gstatic.com' ||
  url.hostname === 'cdn.jsdelivr.net';

self.addEventListener('fetch', e => {
  const req = e.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);
  if (isRuntime(url)) {          // cache first
    e.respondWith(caches.open(RUNTIME).then(async c => {
      const hit = await c.match(req);
      if (hit) return hit;
      const res = await fetch(req);
      if (res.ok || res.type === 'opaque') c.put(req, res.clone());
      return res;
    }));
    return;
  }
  if (url.origin !== location.origin) return;
  // app files: cache, then refresh in the background (stale-while-revalidate)
  e.respondWith(caches.open(VERSION).then(async c => {
    const hit = await c.match(req, { ignoreSearch: true });
    const fresh = fetch(req).then(res => { if (res.ok) c.put(req, res.clone()); return res; }).catch(() => hit);
    return hit || fresh;
  }));
});
