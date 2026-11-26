// Service worker: deixa o app abrir sem internet.
// Os dados offline ficam no cache do Firestore (IndexedDB); aqui só guardamos as telas e bibliotecas.
const V = 'pdvs-v3';
const SHELL = ['./', './index.html', './app.js', './config.js', './manifest.webmanifest',
  './icon-192.png', './icon-512.png', './icon-maskable-512.png', './apple-touch-icon.png', './favicon-32.png', './logo.png'];
const FB = '10.14.1';
const LIBS = ['app', 'auth', 'firestore'].map(m => `https://www.gstatic.com/firebasejs/${FB}/firebase-${m}.js`);

self.addEventListener('install', e => {
  e.waitUntil(caches.open(V).then(c => c.addAll([...SHELL, ...LIBS])).then(() => self.skipWaiting()));
});
self.addEventListener('activate', e => {
  e.waitUntil(caches.keys().then(ks => Promise.all(ks.filter(k => k !== V).map(k => caches.delete(k)))).then(() => self.clients.claim()));
});
self.addEventListener('fetch', e => {
  const r = e.request, u = new URL(r.url);
  if (r.method !== 'GET') return;
  // Firestore e Auth falam direto com o Google: não interceptar
  if (/googleapis\.com$/.test(u.hostname) || u.hostname.endsWith('firebaseio.com')) return;
  const sameOrigin = u.origin === location.origin;
  const cacheable = sameOrigin || u.hostname === 'www.gstatic.com' || u.hostname === 'fonts.googleapis.com' || u.hostname === 'fonts.gstatic.com';
  if (!cacheable) return;
  if (r.mode === 'navigate') {
    // telas: tenta a rede (pega versão nova), cai pro cache sem sinal
    e.respondWith(fetch(r).then(res => { const c = res.clone(); caches.open(V).then(k => k.put('./index.html', c)); return res; })
      .catch(() => caches.match('./index.html')));
    return;
  }
  // demais arquivos: cache primeiro, atualiza por trás
  e.respondWith(caches.match(r).then(hit => {
    const net = fetch(r).then(res => { if (res.ok || res.type === 'opaque') { const c = res.clone(); caches.open(V).then(k => k.put(r, c)); } return res; }).catch(() => hit);
    return hit || net;
  }));
});
