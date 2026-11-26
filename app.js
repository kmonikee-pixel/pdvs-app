import { initializeApp } from 'https://www.gstatic.com/firebasejs/10.14.1/firebase-app.js';
import { getAuth, onAuthStateChanged, signInWithEmailAndPassword, signOut, sendPasswordResetEmail, createUserWithEmailAndPassword } from 'https://www.gstatic.com/firebasejs/10.14.1/firebase-auth.js';
import { initializeFirestore, persistentLocalCache, persistentMultipleTabManager, collection, doc, onSnapshot, setDoc, updateDoc, deleteDoc, addDoc, arrayUnion, writeBatch } from 'https://www.gstatic.com/firebasejs/10.14.1/firebase-firestore.js';
import { firebaseConfig, ADMIN_EMAIL } from './config.js';

/* ---------- utilidades ---------- */
const $ = s => document.querySelector(s);
const clone = x => JSON.parse(JSON.stringify(x));
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const D = s => { const [y, m, d] = String(s).split('-').map(Number); return Math.round(Date.UTC(y, m - 1, d) / 864e5) };
const today = () => { const t = new Date(); return new Date(t.getTime() - t.getTimezoneOffset() * 6e4).toISOString().slice(0, 10) };
const addD = (s, n) => new Date((D(s) + n) * 864e5).toISOString().slice(0, 10);
const fd = s => s ? s.slice(8, 10) + '/' + s.slice(5, 7) : '—';
const rel = n => n === 0 ? 'hoje' : n === 1 ? 'amanhã' : n === -1 ? 'ontem' : n < 0 ? `há ${-n} dias` : `em ${n} dias`;
const brl = v => (+v || 0).toLocaleString('pt-BR', { style: 'currency', currency: 'BRL' });
const nf = v => (Math.round((+v || 0) * 10) / 10).toLocaleString('pt-BR');
const rid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 7);
const has = v => v !== null && v !== undefined && v !== '';
const ST = { ativo: 'Ativo', prospeccao: 'Prospecção', inativo: 'Inativo', verificar: 'A verificar', fechou: 'Não existe mais' };
const TIPOS = ['Tabacaria', 'Banca', 'Depósito / distribuidora', 'Mercado / conveniência', 'Bar / lanchonete', 'Barbearia', 'Outro'];
const PAPEIS = { admin: 'Administradora', vendedor: 'Vendedor', leitura: 'Só leitura' };
const DEF = { unidade: 'caixa', preco: 0, ciclo: 15, ptsCaixa: 10, ptsPontual: 5, ptsIndicacao: 30, janela: 90, niveis: [
  { nome: 'Pista', min: 0, premio: 'Preço de tabela e visita garantida no ciclo' },
  { nome: 'Bonde', min: 100, premio: 'Brinde em cada pedido (piteira, isqueiro ou bag)' },
  { nome: 'Quebrada', min: 250, premio: '1 caixa bônus a cada 10 compradas' },
  { nome: 'Coroa', min: 500, premio: '10% off, display de vitrine e destaque no Instagram da marca' }] };

/* ---------- estado ---------- */
let app, auth, db, me = null, started = false, unsubs = [];
let pdvs = new Map(), evs = [], peds = [], bons = [], cfg = clone(DEF), acessos = new Map(), M = new Map();
let impTxt = '', pending = 0, cached = true, F = { q: '', st: '', cid: '', tipo: '', sort: 'nome' }, rcid = '', per = 90, skip = new Set(), undo = null, openId = null, installEvt = null, ip = 'mes', iv = 'eu';
const can = { write: () => me && me.papel !== 'leitura', admin: () => me && me.papel === 'admin' };

/* ---------- inicialização ---------- */
if ('serviceWorker' in navigator) addEventListener('load', () => navigator.serviceWorker.register('sw.js').catch(() => {}));
addEventListener('beforeinstallprompt', e => { e.preventDefault(); installEvt = e; if (location.hash === '#mais') render() });
{ let h = '', x = 0, i = 0; const r = n => ((Math.sin(n * 12.9898) * 43758.5453) % 1 + 1) % 1;
  while (x < 560) { const w = 26 + r(i) * 30, hh = 30 + r(i + 7) * 90 + (x / 560) * 20; h += `<rect x="${x}" y="${150 - hh}" width="${w - 3}" height="${hh}" fill="#fff"/>`; x += w; i++ }
  $('#sky').innerHTML = h }

function gate(msg, { login = false, out = false } = {}) {
  $('#app').hidden = true; $('#gate').hidden = false; $('#gateMsg').textContent = msg;
  $('#loginF').hidden = !login; $('#gateOut').hidden = !out }

if (!firebaseConfig.apiKey || firebaseConfig.apiKey === 'COLE_AQUI') {
  gate('O app ainda não foi ligado ao banco de dados. Falta colar a configuração do Firebase em config.js.');
} else {
  app = initializeApp(firebaseConfig);
  auth = getAuth(app);
  db = initializeFirestore(app, { localCache: persistentLocalCache({ tabManager: persistentMultipleTabManager() }) });
  onAuthStateChanged(auth, u => { stopAll(); if (!u) return gate('Entre com o e-mail e a senha que a administradora te passou.', { login: true }); resolveRole(u) });
}

$('#loginF').addEventListener('submit', async e => {
  e.preventDefault(); const f = e.target.elements, er = $('#loginErr'); er.hidden = true;
  try { await signInWithEmailAndPassword(auth, f.email.value.trim(), f.senha.value) }
  catch (x) { er.hidden = false; er.textContent = !navigator.onLine ? 'Sem internet. O primeiro login precisa de sinal; depois o app funciona offline.' : /invalid|wrong|user-not-found/.test(x.code) ? 'E-mail ou senha incorretos.' : x.code === 'auth/too-many-requests' ? 'Muitas tentativas. Espere alguns minutos.' : 'Não deu para entrar (' + x.code + ').' }
});
$('#forgot').onclick = async () => {
  const em = $('#loginF').elements.email.value.trim(), er = $('#loginErr'); er.hidden = false;
  if (!em) { er.textContent = 'Digite seu e-mail acima e toque de novo em "Esqueci minha senha".'; return }
  try { await sendPasswordResetEmail(auth, em); er.textContent = 'Se esse e-mail tiver acesso, chegou um link para criar nova senha. Olhe também o spam.' } catch { er.textContent = 'Não consegui enviar agora. Tente com internet.' }
};
$('#gateOut').onclick = () => signOut(auth);

function stopAll() { unsubs.forEach(u => u()); unsubs = []; started = false; me = null; pdvs = new Map(); bons = []; acessos = new Map() }

function resolveRole(u) {
  const email = (u.email || '').toLowerCase();
  const isRoot = email === ADMIN_EMAIL.toLowerCase();
  gate('Conferindo seu acesso…');
  unsubs.push(onSnapshot(doc(db, 'acessos', email), s => {
    const a = s.exists() ? s.data() : null;
    if (isRoot) me = { email, nome: a?.nome || 'Administradora', papel: 'admin' };
    else if (!a) { me = null; return gate(`O e-mail ${email} ainda não tem acesso. Peça para a administradora liberar.`, { out: true }) }
    else if (!a.ativo) { me = null; return gate('Seu acesso está desativado. Fale com a administradora.', { out: true }) }
    else me = { email, nome: a.nome || email, papel: a.papel || 'vendedor' };
    document.body.classList.toggle('ro', !can.write()); document.body.classList.toggle('notadm', !can.admin());
    $('#whoName').textContent = me.nome === PAPEIS[me.papel] ? me.nome : `${me.nome} · ${PAPEIS[me.papel]}`;
    document.querySelectorAll('[data-admin]').forEach(a => a.hidden = !can.admin());
    if (!started) startData();
    $('#gate').hidden = true; $('#app').hidden = false; render();
  }, e => gate(isRoot ? 'Não consegui ler o banco. Confira se as regras de segurança foram publicadas no Firebase.' : 'Sem permissão para acessar. Fale com a administradora.', { out: true })));
}

function startData() {
  started = true;
  const fail = e => { if (e?.code === 'permission-denied') toast('Sem permissão para ler parte dos dados.') };
  unsubs.push(onSnapshot(collection(db, 'pdvs'), { includeMetadataChanges: true }, s => {
    pdvs = new Map(s.docs.map(d => [d.id, { ...d.data(), id: d.id }]));
    pending = s.docs.filter(d => d.metadata.hasPendingWrites).length; cached = s.metadata.fromCache;
    flatten(); net(); render();
  }, fail));
  unsubs.push(onSnapshot(collection(db, 'bonus'), s => { bons = s.docs.map(d => ({ ...d.data(), id: d.id })); render() }, fail));
  unsubs.push(onSnapshot(doc(db, 'config', 'geral'), s => { cfg = s.exists() ? { ...clone(DEF), ...s.data() } : clone(DEF); if (!Array.isArray(cfg.niveis) || cfg.niveis.length !== 4) cfg.niveis = clone(DEF.niveis); render() }, fail));
  if (can.admin()) unsubs.push(onSnapshot(collection(db, 'acessos'), s => { acessos = new Map(s.docs.map(d => [d.id, d.data()])); if (cur() === 'equipe') render() }, fail));
}
function flatten() { evs = []; for (const p of pdvs.values()) for (const e of (p.hist || [])) evs.push({ ...e, pdv: p.id }); peds = evs.filter(e => e.t !== 'v') }
function net() {
  const n = $('#net'), on = navigator.onLine;
  if (!on) { n.classList.add('on'); $('#netMsg').textContent = `Sem internet. Pode registrar normal${pending ? `: ${pending} ${pending === 1 ? 'ponto alterado vai' : 'pontos alterados vão'} subir quando o sinal voltar` : ', tudo sobe quando o sinal voltar'}.` }
  else if (pending) { n.classList.add('on'); $('#netMsg').textContent = `Enviando ${pending} ${pending === 1 ? 'alteração' : 'alterações'}…` }
  else n.classList.remove('on');
}
addEventListener('online', () => { net(); render() }); addEventListener('offline', () => { net(); render() });

/* ---------- cálculos ---------- */
const U = () => cfg.unidade || 'caixa';
const Us = n => n === 1 ? U() : U() + 's';
function nivelDe(pts) { let n = 0; cfg.niveis.forEach((t, i) => { if (pts >= +t.min) n = i }); return n }
const byD = (a, b) => a.d < b.d ? -1 : a.d > b.d ? 1 : (a.em || 0) - (b.em || 0);
function derive() {
  M = new Map(); const t = D(today()), j = +cfg.janela || 90;
  const indic = new Map(); for (const p of pdvs.values()) if (p.indicadoPor && p.status === 'ativo') indic.set(p.indicadoPor, (indic.get(p.indicadoPor) || 0) + 1);
  for (const p of pdvs.values()) {
    const ev = (p.hist || []).slice().sort(byD), ps = ev.filter(e => e.t !== 'v');
    const s = { ev, ps, n: ps.length, qtd: 0, valor: 0, receber: 0, last: ps[ps.length - 1] || null, lastEv: ev[ev.length - 1] || null, giro: 0, medido: false, ciclo: 0, prox: null, dAte: null, pts: 0 };
    ps.forEach(o => { s.qtd += +o.q || 0; s.valor += +o.v || 0; if (o.pg === 'receber') s.receber += +o.v || 0 });
    const gaps = []; for (let i = 1; i < ps.length; i++) gaps.push(Math.max(1, D(ps[i].d) - D(ps[i - 1].d)));
    s.ciclo = +p.ciclo || (gaps.length ? Math.round(gaps.reduce((a, b) => a + b, 0) / gaps.length) : +cfg.ciclo || 15);
    // giro: estoque deixado no ponto x sobra encontrada na visita seguinte
    let stock = null, sold = 0, d0 = null, d1 = null, stockD = null;
    for (const e of ev) {
      if (stock !== null) {
        if (has(e.s)) { sold += Math.max(0, stock - (+e.s)); stock = +e.s; d1 = e.d; s.medido = true }
        else if (e.t !== 'v') { sold += stock; stock = 0; d1 = e.d }
      } else if (has(e.s)) { stock = +e.s; d0 = e.d }
      if (e.t !== 'v') { if (stock === null) { stock = 0; d0 = e.d } stock += +e.q || 0 }
      if (e.t !== 'v' || has(e.s)) stockD = e.d;
    }
    if (d0 && d1 && D(d1) > D(d0)) s.giro = sold / (D(d1) - D(d0)) * 7;
    if (s.last) {
      if (s.giro > 0 && !p.ciclo && stock !== null) s.prox = addD(stockD, Math.max(0, Math.round(stock / (s.giro / 7))));
      else s.prox = addD(s.last.d, s.ciclo);
      s.dAte = D(s.prox) - t;
    }
    ps.forEach((o, i) => { if (t - D(o.d) <= j) { s.pts += (+o.q || 0) * (+cfg.ptsCaixa || 0); if (i && D(o.d) - D(ps[i - 1].d) <= s.ciclo + 3) s.pts += +cfg.ptsPontual || 0 } });
    s.ind = indic.get(p.id) || 0; s.pts += s.ind * (+cfg.ptsIndicacao || 0); s.nivel = nivelDe(s.pts);
    M.set(p.id, s);
  }
}
const FP = ['PIX', 'Dinheiro', 'Cartão', 'Boleto', 'A prazo'];
const brD = s => s ? s.slice(8, 10) + '/' + s.slice(5, 7) + '/' + s.slice(0, 4) : '';
const emp = () => cfg.empresa || {};
function produtos() { const l = Array.isArray(cfg.produtos) && cfg.produtos.length ? cfg.produtos : [{ c: 'SDF-CX', d: 'Seda de Favela (caixa)', un: 'CX', p: +cfg.preco || 0, ncm: '4813.10.00', f: 1 }]; return l }
const prodDe = c => produtos().find(x => x.c === c);
function itensDe(o) { if (Array.isArray(o.it) && o.it.length) return o.it; if (o.t === 'v' || !+o.q) return []; const p0 = produtos()[0]; return [{ c: p0.c, d: p0.d, un: p0.un, ncm: p0.ncm, q: +o.q, pu: +o.q ? (+o.v || 0) / +o.q : 0 }] }
const subtotal = o => itensDe(o).reduce((a, i) => a + (+i.q || 0) * (+i.pu || 0), 0);
function numPedido(d) {
  const ini = (me.nome || me.email).normalize('NFD').replace(/[^A-Za-z]/g, '').slice(0, 3).toUpperCase() || 'VEN';
  const pre = `SDF-${d.slice(2, 4)}${d.slice(5, 7)}${d.slice(8, 10)}-${ini}-`;
  const n = evs.filter(e => (e.n || '').startsWith(pre)).length + 1;
  return pre + String(n).padStart(2, '0') }
function faltaNF(p) { const e = emp(), f = [];
  if (!p.doc) f.push('CPF/CNPJ do cliente'); if (!p.endereco) f.push('endereço do cliente'); if (!p.cep) f.push('CEP do cliente'); if (!p.cidade || !p.uf) f.push('cidade/UF do cliente');
  if (!e.doc) f.push('CNPJ da empresa (Ajustes)'); if (!e.ie) f.push('inscrição estadual da empresa (Ajustes)');
  return f }
const qtdEm = (id, dias) => { const t = D(today()); return (M.get(id)?.ps || []).filter(o => dias === 0 || t - D(o.d) < dias).reduce((a, o) => a + (+o.q || 0), 0) };
const lugar = p => [p.bairro, p.cidade && (p.cidade + (p.uf ? '/' + p.uf : ''))].filter(Boolean).join(' · ') || 'Sem local';
const pill = st => `<span class="pill p-${esc(st)}">${esc(ST[st] || st)}</span>`;
const tier = i => `<span class="tier ${i === 3 ? 't3' : ''}">${esc(cfg.niveis[i]?.nome)}</span>`;
function wa(p, msg) { const d = String(p.contato || '').replace(/\D/g, ''); if (d.length < 10) return ''; const n = d.length <= 11 ? '55' + d : d;
  return `<a class="btn sm line" href="https://wa.me/${n}?text=${encodeURIComponent(msg || 'Oi, tudo certo? Aqui é da Seda de Favela. Passando pra ver como tá o estoque de seda aí. Bora repor?')}" target="_blank" rel="noopener">WhatsApp</a>` }
const mapa = p => `<a class="btn sm line" href="https://www.google.com/maps/search/?api=1&query=${encodeURIComponent(p.endereco || [p.nome, p.bairro, p.cidade, p.uf].filter(Boolean).join(' '))}" target="_blank" rel="noopener">Mapa</a>`;
const lbl = p => p.nome + ' — ' + (p.cidade || 'sem cidade');

function kpis() {
  const all = [...pdvs.values()], at = all.filter(p => p.status === 'ativo'), t = D(today());
  const rep = at.filter(p => { const s = M.get(p.id); return s.prox && s.dAte <= 3 }).length;
  const q30 = peds.filter(o => t - D(o.d) < 30).reduce((a, o) => a + (+o.q || 0), 0), q60 = peds.filter(o => t - D(o.d) >= 30 && t - D(o.d) < 60).reduce((a, o) => a + (+o.q || 0), 0);
  const rec = peds.filter(o => o.pg === 'receber').reduce((a, o) => a + (+o.v || 0), 0);
  const ver = all.filter(p => p.status === 'verificar').length, pro = all.filter(p => p.status === 'prospeccao').length, d = q30 - q60;
  $('#kpis').innerHTML = `
  <button class="kpi ${rep ? 'hot' : ''}" data-go="repor"><span class="num">${rep}</span><small>pra repor até 3 dias</small></button>
  <button class="kpi" data-go="pontos" data-st="ativo"><span class="num">${at.length}</span><small>pontos ativos</small></button>
  <div class="kpi"><span class="num">${nf(q30)}</span><small>${esc(U())}s em 30 dias${q60 || q30 ? ` · ${d >= 0 ? '+' : ''}${nf(d)}` : ''}</small></div>
  <div class="kpi"><span class="num">${rec ? brl(rec) : 'R$ 0'}</span><small>a receber</small></div>
  <button class="kpi" data-go="triagem"><span class="num">${ver}</span><small>a verificar · ${pro} prospecção</small></button>`;
  $('#sub').textContent = `${all.length} pontos · ${peds.length} pedidos registrados`;
  const tb = $('#tabs a[data-tri]'); tb.innerHTML = 'Triagem' + (ver ? ` <b>${ver}</b>` : '');
}

/* ---------- telas ---------- */
function rcard(p) { const s = M.get(p.id), late = s.dAte < 0;
  return `<div class="card ${late ? 'late' : ''}"><div class="ct"><div><button class="nm" data-act="open" data-id="${esc(p.id)}">${esc(p.nome)}</button><div class="pl">${esc(lugar(p))}</div></div>
  <div class="due"><span class="num">${fd(s.prox)}</span><small>${late ? 'atrasado ' : ''}${rel(s.dAte)}</small></div></div>
  <div class="meta"><span>Último pedido <b>${fd(s.last.d)}</b> · ${nf(s.last.q)} ${esc(Us(+s.last.q))}</span>${s.lastEv && s.lastEv.t === 'v' ? `<span>Visita <b>${fd(s.lastEv.d)}</b></span>` : ''}${s.giro ? `<span>Giro <b>${nf(s.giro)}/sem</b>${s.medido ? '' : ' (estimado)'}</span>` : ''}<span>${tier(s.nivel)}</span></div>
  <div class="cb"><button class="btn sm ink" data-w data-act="newPed" data-id="${esc(p.id)}">Registrar</button>${wa(p)}${mapa(p)}</div></div>` }

function vRepor() {
  const at = [...pdvs.values()].filter(p => p.status === 'ativo');
  const cids = [...new Set(at.filter(p => M.get(p.id).last).map(p => p.cidade).filter(Boolean))].sort();
  const wl = at.filter(p => M.get(p.id).last && (!rcid || p.cidade === rcid)).sort((a, b) => M.get(a.id).dAte - M.get(b.id).dAte);
  const g = [['Atrasados', wl.filter(p => M.get(p.id).dAte < 0)], ['Hoje até 3 dias', wl.filter(p => { const d = M.get(p.id).dAte; return d >= 0 && d <= 3 })], ['Esta semana', wl.filter(p => { const d = M.get(p.id).dAte; return d > 3 && d <= 7 })], ['Mais pra frente', wl.filter(p => M.get(p.id).dAte > 7)]];
  const semPed = at.filter(p => !M.get(p.id).last && (!rcid || p.cidade === rcid)), pro = [...pdvs.values()].filter(p => p.status === 'prospeccao' && (!rcid || p.cidade === rcid)).sort((a, b) => (a.proxContato || '9') < (b.proxContato || '9') ? -1 : 1);
  const ver = [...pdvs.values()].filter(p => p.status === 'verificar').length;
  let h = `<h2>Quem repor</h2><p class="lead">A data vem do ritmo de cada ponto. Anote a sobra que encontrar em cada visita, mesmo sem pedido: é ela que mostra quanto o ponto vende por semana.</p>`;
  if (cids.length > 1) h += `<div class="chips"><button class="chip ${!rcid ? 'on' : ''}" data-act="rcid" data-v="">Todas</button>${cids.map(c => `<button class="chip ${rcid === c ? 'on' : ''}" data-act="rcid" data-v="${esc(c)}">${esc(c)}</button>`).join('')}</div>`;
  if (!peds.length) h += `<div class="hero"><div><h3 style="margin-top:0">Comece por aqui</h3><ol class="steps">
   <li><b>Triagem:</b> marque quem está ativo, inativo ou fechou. Um toque por ponto.</li>
   <li><b>Registre o último pedido</b> de cada ativo. É isso que liga a previsão.</li>
   <li>Na rua, a cada visita: botão <b>+</b>, e anote a sobra que encontrou.</li></ol>
   <div class="cb" style="margin-top:12px"><a class="btn ink" href="#triagem">Abrir triagem</a></div></div>
   <div><span class="num">${ver}</span><div class="pl">pontos esperando triagem</div></div></div>`;
  for (const [t, l] of g) if (l.length) h += `<h3>${t} <span>${l.length}</span></h3><div class="grid">${l.slice(0, t === 'Mais pra frente' ? 12 : 99).map(rcard).join('')}</div>`;
  if (semPed.length) h += `<h3>Ativos sem pedido registrado <span>${semPed.length}</span></h3><div class="grid">${semPed.slice(0, 30).map(p => `<div class="card"><div class="ct"><div><button class="nm" data-act="open" data-id="${esc(p.id)}">${esc(p.nome)}</button><div class="pl">${esc(lugar(p))}</div></div></div><div class="cb"><button class="btn sm ink" data-w data-act="newPed" data-id="${esc(p.id)}">Registrar</button>${wa(p)}</div></div>`).join('')}</div>`;
  if (pro.length) h += `<h3>Prospecção: retornos <span>${pro.length}</span></h3><div class="grid">${pro.slice(0, 30).map(p => { const d = p.proxContato ? D(p.proxContato) - D(today()) : null; return `<div class="card ${d !== null && d < 0 ? 'late' : ''}"><div class="ct"><div><button class="nm" data-act="open" data-id="${esc(p.id)}">${esc(p.nome)}</button><div class="pl">${esc(lugar(p))}</div></div><div class="due"><span class="num">${p.proxContato ? fd(p.proxContato) : '—'}</span><small>${d === null ? 'sem data' : rel(d)}</small></div></div>${p.obs ? `<div class="meta">${esc(p.obs)}</div>` : ''}<div class="cb"><button class="btn sm ink" data-w data-act="newPed" data-id="${esc(p.id)}">Fechou pedido</button>${wa(p, 'Oi, tudo certo? Aqui é da Seda de Favela, passei aí esses dias. Bora fechar o primeiro pedido de seda?')}<button class="btn sm line" data-w data-act="edit" data-id="${esc(p.id)}">Editar</button></div></div>` }).join('')}</div>`;
  return h }

function vPontos() {
  const all = [...pdvs.values()], cids = [...new Set(all.map(p => p.cidade).filter(Boolean))].sort(), q = F.q.trim().toLowerCase();
  let l = all.filter(p => (!F.st || p.status === F.st) && (!F.cid || p.cidade === F.cid) && (!F.tipo || p.tipo === F.tipo) && (!q || [p.nome, p.bairro, p.cidade, p.endereco, p.contato].join(' ').toLowerCase().includes(q)));
  const S = { nome: (a, b) => a.nome.localeCompare(b.nome), prox: (a, b) => (M.get(a.id).dAte ?? 1e9) - (M.get(b.id).dAte ?? 1e9), compra: (a, b) => qtdEm(b.id, 90) - qtdEm(a.id, 90), ult: (a, b) => (M.get(b.id).last?.d || '') > (M.get(a.id).last?.d || '') ? 1 : -1 };
  l.sort(S[F.sort]);
  const opt = (v, t, c) => `<option value="${esc(v)}" ${c === v ? 'selected' : ''}>${esc(t)}</option>`;
  return `<h2>Todos os pontos</h2><p class="lead">${l.length} de ${all.length} pontos.</p>
  <div class="bar"><input id="fq" type="search" placeholder="Buscar nome, bairro, telefone…" value="${esc(F.q)}" aria-label="Buscar">
  <select id="fst" aria-label="Status">${opt('', 'Todos os status', F.st)}${Object.entries(ST).map(([k, v]) => opt(k, v, F.st)).join('')}</select>
  <select id="fcid" aria-label="Cidade">${opt('', 'Todas as cidades', F.cid)}${cids.map(c => opt(c, c, F.cid)).join('')}</select>
  <select id="ftipo" aria-label="Tipo">${opt('', 'Todos os tipos', F.tipo)}${TIPOS.map(t => opt(t, t, F.tipo)).join('')}</select>
  <select id="fsort" aria-label="Ordenar">${opt('nome', 'A a Z', F.sort)}${opt('prox', 'Próxima reposição', F.sort)}${opt('compra', 'Mais compram (90 dias)', F.sort)}${opt('ult', 'Pedido mais recente', F.sort)}</select>
  <button class="btn line" data-w data-act="newPdv">+ Ponto</button></div>
  ${l.length ? `<table class="stack"><thead><tr><th>Ponto</th><th>Status</th><th>Tipo</th><th>Último pedido</th><th>Repor</th><th class="r">${esc(U())}s 90d</th><th>Nível</th></tr></thead><tbody>
  ${l.map(p => { const s = M.get(p.id); return `<tr tabindex="0" data-act="open" data-id="${esc(p.id)}"><td><b>${esc(p.nome)}</b><div class="pl">${esc(lugar(p))}</div></td><td>${pill(p.status)}${p.flags?.length ? ' <span class="pill">!</span>' : ''}</td><td>${esc(p.tipo)}</td><td>${s.last ? fd(s.last.d) : ''}</td><td>${s.prox && p.status === 'ativo' ? `${fd(s.prox)} <span class="pl">${rel(s.dAte)}</span>` : ''}</td><td class="r">${s.n ? nf(qtdEm(p.id, 90)) : ''}</td><td>${s.n ? tier(s.nivel) : ''}</td></tr>` }).join('')}</tbody></table>` : `<div class="empty">Nenhum ponto com esses filtros.</div>`}` }

function lista(t, rows, fmt) { const mx = Math.max(1, ...rows.map(r => r.v));
  return `<div class="rk"><h3>${t}</h3>${rows.length ? rows.map((r, i) => `<div class="rr" ${r.id ? `data-act="open" data-id="${esc(r.id)}"` : ''}><i>${i + 1}</i><span class="n">${esc(r.n)}</span><span class="v">${fmt(r.v)}</span><div class="tr"><div style="width:${(r.v / mx * 100).toFixed(1)}%"></div></div></div>`).join('') : '<p class="pl">Sem pedidos nesse período.</p>'}</div>` }
function vRanking() {
  const t = D(today()), ps = peds.filter(o => per === 0 || t - D(o.d) < per), agg = new Map(), ven = new Map(), cid = new Map();
  for (const o of ps) { const a = agg.get(o.pdv) || { q: 0, n: 0 }; a.q += +o.q || 0; a.n++; agg.set(o.pdv, a); const v = o.pn || o.por || 'Painel antigo'; ven.set(v, (ven.get(v) || 0) + (+o.q || 0)); const c = pdvs.get(o.pdv)?.cidade || 'Sem cidade'; cid.set(c, (cid.get(c) || 0) + (+o.q || 0)) }
  const nm = id => pdvs.get(id)?.nome || 'Ponto removido', top = a => a.sort((x, y) => y.v - x.v).slice(0, 10);
  const P = [[30, '30 dias'], [90, '90 dias'], [365, '12 meses'], [0, 'Tudo']];
  return `<h2>Ranking</h2><p class="lead">"Mais vendem" é o giro: quanto sai do ponto por semana, medido pela sobra anotada nas visitas.</p>
  <div class="chips">${P.map(([v, l]) => `<button class="chip ${per === v ? 'on' : ''}" data-act="per" data-v="${v}">${l}</button>`).join('')}</div>
  <div class="cols">${lista(`Mais compram (${esc(U())}s)`, top([...agg].map(([id, a]) => ({ id, n: nm(id), v: a.q }))), nf)}
  ${lista(`Mais vendem (${esc(U())}s/semana)`, top([...pdvs.values()].map(p => ({ id: p.id, n: p.nome, v: M.get(p.id).giro })).filter(r => r.v > 0)), nf)}
  ${lista('Mais pedidos feitos', top([...agg].map(([id, a]) => ({ id, n: nm(id), v: a.n }))), v => v)}
  ${lista(`Por vendedor (${esc(U())}s)`, top([...ven].map(([n, v]) => ({ n, v }))), nf)}
  ${lista(`Por cidade (${esc(U())}s)`, top([...cid].map(([n, v]) => ({ n, v }))), nf)}</div>` }

function vBonus() {
  const at = [...pdvs.values()].filter(p => p.status === 'ativo' && M.get(p.id).n).sort((a, b) => M.get(b.id).pts - M.get(a.id).pts);
  const cnt = cfg.niveis.map((_, i) => at.filter(p => M.get(p.id).nivel === i).length);
  return `<h2>Programa de bonificação</h2><p class="lead">Conta os últimos ${+cfg.janela} dias. Cada ${esc(U())} vale <b>${+cfg.ptsCaixa} pts</b>, repor no prazo vale <b>+${+cfg.ptsPontual}</b>, indicar um ponto que virou cliente vale <b>+${+cfg.ptsIndicacao}</b>.</p>
  <div class="tiers">${cfg.niveis.map((t, i) => `<div class="tc ${i === 3 ? 'top3' : ''}"><span class="num">${esc(t.nome)}</span><span class="q">a partir de ${+t.min} pts · ${cnt[i]} ${cnt[i] === 1 ? 'ponto' : 'pontos'}</span><span>${esc(t.premio)}</span></div>`).join('')}</div>
  <h3>Clientes no programa <span>${at.length}</span></h3>
  ${at.length ? `<table class="stack"><thead><tr><th>Ponto</th><th>Nível</th><th class="r">Pontos</th><th>Até o próximo</th><th class="r">${esc(U())}s ${+cfg.janela}d</th><th></th></tr></thead><tbody>${at.map(p => { const s = M.get(p.id), nx = cfg.niveis[s.nivel + 1], b = s.nivel ? +cfg.niveis[s.nivel].min : 0;
   return `<tr data-act="open" data-id="${esc(p.id)}" tabindex="0"><td><b>${esc(p.nome)}</b><div class="pl">${esc(lugar(p))}</div></td><td>${tier(s.nivel)}</td><td class="r"><b>${s.pts}</b></td><td>${nx ? `<span class="prog"><div style="width:${Math.min(100, (s.pts - b) / (nx.min - b) * 100).toFixed(0)}%"></div></span>${nx.min - s.pts} pts pra ${esc(nx.nome)}` : 'Topo'}</td><td class="r">${nf(qtdEm(p.id, +cfg.janela))}</td><td><button class="btn sm line" data-adm data-act="bonif" data-id="${esc(p.id)}">Bonificar</button></td></tr>` }).join('')}</tbody></table>` : `<div class="empty">Os clientes entram aqui quando estão ativos e têm pedido registrado.</div>`}
  <h3>Bonificações entregues <span>${bons.length}</span></h3>
  ${bons.length ? `<ul class="hist">${[...bons].sort((a, b) => a.data < b.data ? 1 : -1).slice(0, 40).map(b => `<li><span><b>${esc(pdvs.get(b.pdv)?.nome || 'Ponto removido')}</b> · ${fd(b.data)}<br><span class="pl">${esc(b.desc)}</span></span><button class="lk" data-adm data-act="delBon" data-id="${esc(b.id)}">Remover</button></li>`).join('')}</ul>` : `<div class="empty">Quando entregar um prêmio, toque em Bonificar para ficar registrado.</div>`}` }

function vTriagem() {
  const all = [...pdvs.values()].filter(p => p.status === 'verificar').sort((a, b) => (a.linha || 9e9) - (b.linha || 9e9));
  const tot = pdvs.size, done = tot - all.length, p = all.find(p => !skip.has(p.id));
  if (!all.length) return `<div class="tri"><h2>Triagem completa</h2><p class="lead">Nenhum ponto esperando verificação.</p><a class="btn ink" href="#repor">Ir para reposição</a></div>`;
  if (!p) return `<div class="tri"><h2>Você pulou os ${all.length} que faltam</h2><button class="btn ink" data-act="unskip">Recomeçar pelos pulados</button></div>`;
  return `<div class="tri"><h2>Triagem</h2><p class="lead">${done} de ${tot} resolvidos.</p><div class="meter"><div style="width:${(done / tot * 100).toFixed(1)}%"></div></div>
  <div class="card"><div class="pl">${esc(p.tipo)} · ${esc(lugar(p))}</div><div class="nm">${esc(p.nome)}</div>
  ${p.endereco ? `<div>${esc(p.endereco)}</div>` : ''}${p.contato ? `<div><b>${esc(p.contato)}</b></div>` : ''}
  ${(p.flags || []).map(f => `<div class="flag">${esc(f)}</div>`).join('')}
  <div class="cb">${wa(p, 'Oi, tudo certo? Aqui é da Seda de Favela. Vocês ainda trabalham com seda? Queria saber como tá o estoque aí.')}${mapa(p)}<button class="btn sm line" data-w data-act="edit" data-id="${esc(p.id)}">Editar dados</button></div>
  <div class="tb" data-w><button class="btn ok" data-act="tri" data-st="ativo" data-id="${esc(p.id)}">Ativo, compra com a gente</button><button class="btn sun" data-act="tri" data-st="prospeccao" data-id="${esc(p.id)}">Prospectar de novo</button>
  <button class="btn line" data-act="tri" data-st="inativo" data-id="${esc(p.id)}">Inativo, parou de pedir</button><button class="btn line" data-act="tri" data-st="fechou" data-id="${esc(p.id)}">Não existe mais</button></div>
  <button class="btn sm line" style="align-self:center" data-act="skip" data-id="${esc(p.id)}">Não sei ainda, pular</button></div></div>` }

function vEquipe() {
  if (!can.admin()) return `<div class="empty">Só a administradora vê a equipe.</div>`;
  const l = [...acessos].sort((a, b) => (a[1].nome || '').localeCompare(b[1].nome || ''));
  const cnt = new Map(); for (const o of peds) if (o.por) cnt.set(o.por, (cnt.get(o.por) || 0) + 1);
  return `<h2>Equipe</h2><p class="lead">Cada pessoa entra com o próprio e-mail e senha. <b>Vendedor</b> cadastra pontos, registra pedidos e visitas e faz triagem. <b>Só leitura</b> vê tudo e não altera nada. Desativar corta o acesso na hora, sem apagar o que a pessoa registrou.</p>
  <form id="teamF" class="f card" style="padding:18px;margin-bottom:18px">
   <label>Nome<input name="nome" required autocomplete="off"></label>
   <label>E-mail<input name="email" type="email" required autocomplete="off"></label>
   <label>Papel<select name="papel"><option value="vendedor">Vendedor</option><option value="leitura">Só leitura</option><option value="admin">Administradora</option></select></label>
   <label>Senha inicial<input name="senha" minlength="6" required autocomplete="new-password"><small>Mínimo 6 caracteres. Passe para a pessoa e peça para trocar em "Esqueci minha senha".</small></label>
   <div class="fa w"><button class="btn ink">Dar acesso</button></div></form>
  ${l.length ? `<table class="stack"><thead><tr><th>Pessoa</th><th>Papel</th><th>Status</th><th class="r">Registros</th><th></th></tr></thead><tbody>${l.map(([em, a]) => `<tr><td><b>${esc(a.nome)}</b><div class="pl">${esc(em)}</div></td>
   <td><select data-act="papel" data-id="${esc(em)}" aria-label="Papel" ${em === me.email ? 'disabled' : ''}>${Object.entries(PAPEIS).map(([k, v]) => `<option value="${k}" ${a.papel === k ? 'selected' : ''}>${v}</option>`).join('')}</select></td>
   <td>${a.ativo ? '<span class="pill p-ativo">Ativo</span>' : '<span class="pill p-inativo">Desativado</span>'}</td><td class="r">${cnt.get(em) || 0}</td>
   <td>${em === me.email ? '' : `<button class="lk" data-act="ativo" data-id="${esc(em)}">${a.ativo ? 'Desativar' : 'Reativar'}</button>`}<button class="lk" data-act="reset" data-id="${esc(em)}">Link de nova senha</button></td></tr>`).join('')}</tbody></table>` : '<div class="empty">Ninguém além de você ainda.</div>'}` }

function vNotas() {
  if (!can.admin()) return '<div class="empty">Só a administradora controla as notas.</div>';
  const l = peds.filter(o => o.nf).sort((a, b) => a.d < b.d ? 1 : -1), pend = l.filter(o => o.nf.st !== 'emitida'), emi = l.filter(o => o.nf.st === 'emitida');
  const row = o => { const p = pdvs.get(o.pdv) || {}, fl = o.nf.st !== 'emitida' ? faltaNF(p) : [];
    return `<tr><td><b>${esc(o.n || '')}</b><div class="pl">${brD(o.d)} · ${esc(o.pn || '')}</div></td><td>${esc(p.razao || p.nome || 'Ponto removido')}<div class="pl">${esc(p.doc || 'sem CPF/CNPJ')}</div></td><td class="r">${brl(o.v)}</td>
    <td>${o.nf.st === 'emitida' ? `<span class="pill p-ativo">Nº ${esc(o.nf.num)}</span>` : fl.length ? `<span class="pill p-verificar" title="${esc(fl.join(', '))}">falta ${fl.length} dado${fl.length > 1 ? 's' : ''}</span>` : '<span class="pill p-prospeccao">pronta pra emitir</span>'}</td>
    <td><button class="lk" data-act="rec" data-p="${esc(o.pdv)}" data-id="${esc(o.id)}">Comprovante</button>${o.nf.st !== 'emitida' ? `<button class="lk" data-act="notaCopy" data-p="${esc(o.pdv)}" data-id="${esc(o.id)}">Copiar p/ nota</button><button class="lk" data-act="nfOk" data-p="${esc(o.pdv)}" data-id="${esc(o.id)}">Marcar emitida</button>` : ''}</td></tr>` };
  const e = emp(), fe = [!e.doc && 'CNPJ', !e.ie && 'inscrição estadual'].filter(Boolean);
  const ano = today().slice(0, 4), teto = +cfg.tetoMEI || (+ano <= 2026 ? 81000 : +ano === 2027 ? 110000 : 140000);
  const fat = peds.filter(o => o.d.startsWith(ano)).reduce((a, o) => a + (+o.v || 0), 0), mes = +today().slice(5, 7), t0 = D(today()), d1 = peds.length ? Math.min(...peds.map(o => D(o.d))) : t0, jan = Math.max(1, Math.min(90, t0 - d1 + 1)), rec = peds.filter(o => t0 - D(o.d) < jan).reduce((a, o) => a + (+o.v || 0), 0), proj = rec / jan * 365, pct = Math.min(100, fat / teto * 100);
  const mei = `<div class="card" style="margin-bottom:16px"><div class="ct"><div><b>Faturamento ${ano} x teto do MEI</b><div class="pl">Soma dos pedidos registrados no app. Teto de ${brl(teto)} no ano.</div></div><div class="due"><span class="num" style="color:${pct >= 80 ? 'var(--brick)' : 'inherit'}">${brl(fat)}</span><small>${pct.toFixed(0)}% do teto</small></div></div>
   <div class="meter"><div style="width:${pct}%"></div></div><div class="pl">No ritmo dos últimos ${jan} dias, a empresa fatura cerca de <b>${brl(proj)}</b> por ano.${proj > teto ? ' <b style="color:var(--brick)">Passa do teto: converse com a contabilidade sobre sair do MEI.</b>' : ''}</div></div>`;
  return `<h2>Notas fiscais</h2><p class="lead">Cada pedido nasce aqui como <b>a emitir</b>. Emita a NF-e no emissor da empresa (ou mande a planilha para a contabilidade) e marque como emitida com o número. Assim nenhuma venda fica sem nota.</p>
  ${mei}${fe.length ? `<div class="flag" style="margin-bottom:14px">Os dados da empresa estão incompletos (${fe.join(' e ')}). Preencha em <a href="#ajustes">Ajustes</a>.</div>` : ''}
  <div class="cb" style="margin-bottom:14px"><button class="btn ink" data-act="csvNF">Baixar pendentes para o emissor (.csv)</button></div>
  <h3>A emitir <span>${pend.length}</span></h3>${pend.length ? `<table class="stack"><thead><tr><th>Pedido</th><th>Cliente</th><th class="r">Total</th><th>Situação</th><th></th></tr></thead><tbody>${pend.map(row).join('')}</tbody></table>` : '<div class="empty">Nenhuma nota pendente.</div>'}
  <h3>Emitidas <span>${emi.length}</span></h3>${emi.length ? `<table class="stack"><thead><tr><th>Pedido</th><th>Cliente</th><th class="r">Total</th><th>NF-e</th><th></th></tr></thead><tbody>${emi.slice(0, 50).map(row).join('')}</tbody></table>` : '<div class="empty">Nenhuma ainda.</div>'}` }
function nfForm(pid, oid) { openId = null;
  show('Marcar NF-e como emitida', `<form class="f" data-form="nf" data-p="${esc(pid)}" data-id="${esc(oid)}"><label>Número da NF-e<input name="num" required inputmode="numeric"></label><label>Data de emissão<input name="data" type="date" value="${today()}"></label><label class="w">Chave de acesso (opcional)<input name="chave" inputmode="numeric" maxlength="54"></label><div class="fa w"><button type="button" class="btn line" data-act="close">Cancelar</button><button class="btn ink">Salvar</button></div></form>`) }
function csvNF() { const q = x => `"${String(x ?? '').replace(/"/g, '""')}"`, e = emp();
  const rows = [['Pedido', 'Data', 'Cliente (razão social)', 'Nome do ponto', 'CPF/CNPJ', 'IE', 'Endereço', 'Bairro', 'Cidade', 'UF', 'CEP', 'Telefone', 'E-mail', 'Código', 'Produto', 'NCM', 'Unidade', 'Quantidade', 'Valor unitário', 'Valor do item', 'Desconto do pedido', 'Total do pedido', 'Forma de pagamento', 'Situação', 'Vencimento', 'Vendedor', 'Faltam dados']];
  for (const o of peds.filter(o => o.nf && o.nf.st !== 'emitida').sort(byD)) { const p = pdvs.get(o.pdv) || {};
    for (const i of itensDe(o)) rows.push([o.n, brD(o.d), p.razao || p.nome, p.nome, p.doc, p.ie, p.endereco, p.bairro, p.cidade, p.uf, p.cep, p.contato, p.email, i.c, i.d, i.ncm, i.un, i.q, (+i.pu).toFixed(2).replace('.', ','), (i.q * i.pu).toFixed(2).replace('.', ','), (+o.ds || 0).toFixed(2).replace('.', ','), (+o.v).toFixed(2).replace('.', ','), o.fp, o.pg === 'receber' ? 'A receber' : 'Pago', brD(o.venc), o.pn, faltaNF(p).join(', ')]) }
  download(`notas-a-emitir-${today()}.csv`, rows.map(r => r.map(q).join(';')).join('\n')) }

function vAjustes() { const n = cfg.niveis, ad = can.admin();
  return `<h2>Ajustes</h2><p class="lead">${ad ? 'Valem para toda a equipe.' : 'Só a administradora altera as regras.'}</p>
  <form id="cfgF" class="f card" style="padding:20px"><fieldset ${ad ? '' : 'disabled'} style="display:contents">
  <label>Unidade de venda<input name="unidade" value="${esc(cfg.unidade)}" required></label>
  <label>Preço por ${esc(U())} (R$)<input name="preco" type="number" step="0.01" min="0" value="${+cfg.preco}"></label>
  <label>Ciclo padrão de reposição (dias)<input name="ciclo" type="number" min="1" value="${+cfg.ciclo}"></label>
  <label>Janela da bonificação (dias)<input name="janela" type="number" min="7" value="${+cfg.janela}"></label>
  <label>Pontos por ${esc(U())}<input name="ptsCaixa" type="number" min="0" value="${+cfg.ptsCaixa}"></label>
  <label>Bônus por repor no prazo<input name="ptsPontual" type="number" min="0" value="${+cfg.ptsPontual}"></label>
  <label>Bônus por indicação<input name="ptsIndicacao" type="number" min="0" value="${+cfg.ptsIndicacao}"></label><span></span>
  ${n.map((t, i) => `<label>Nível ${i + 1}<input name="n${i}" value="${esc(t.nome)}" required></label><label>A partir de (pts)<input name="m${i}" type="number" min="0" value="${+t.min}" ${i ? '' : 'readonly'}></label><label class="w">Prêmio<input name="p${i}" value="${esc(t.premio)}"></label>`).join('')}
  ${ad ? '<div class="fa w"><button class="btn ink">Salvar ajustes</button></div>' : ''}</fieldset></form>
  ${ad ? `<h3>Dados da empresa (saem no comprovante e na nota)</h3>
  <form id="empF" class="f card" style="padding:20px">${[['razao', 'Razão social', 'w'], ['doc', 'CNPJ (ou CPF)'], ['ie', 'Inscrição estadual'], ['endereco', 'Endereço com número', 'w'], ['bairro', 'Bairro'], ['cidade', 'Cidade'], ['uf', 'UF'], ['cep', 'CEP'], ['tel', 'Telefone / WhatsApp'], ['email', 'E-mail'], ['pix', 'Chave PIX'], ['rodape', 'Texto do rodapé do comprovante', 'w']].map(([k, l, w]) => `<label class="${w || ''}">${l}<input name="${k}" value="${esc(emp()[k])}"></label>`).join('')}
  <label class="w" style="flex-direction:row;gap:10px;align-items:center"><input type="checkbox" name="controlaNF" ${cfg.controlaNF === false ? '' : 'checked'} style="width:22px;min-height:22px"> Controlar emissão de NF-e em cada pedido</label>
  <div class="fa w"><button class="btn ink">Salvar dados da empresa</button></div></form>
  <h3>Produtos</h3><p class="lead">O que aparece para escolher no pedido. "Conta como" diz quantas ${esc(U())}s cada unidade vale no giro e no bônus (0 para brindes e acessórios). Confirme NCM e tributação com a contabilidade.</p>
  <form id="prodF" class="card" style="padding:16px"><table class="stack"><thead><tr><th>Código</th><th>Descrição</th><th>Unid.</th><th>Preço R$</th><th>NCM</th><th>Conta como</th><th></th></tr></thead><tbody>${produtos().map((p, k) => `<tr><td><input name="c${k}" value="${esc(p.c)}" required></td><td><input name="d${k}" value="${esc(p.d)}" required></td><td><input name="un${k}" value="${esc(p.un)}" style="max-width:80px"></td><td><input name="p${k}" type="number" step="0.01" min="0" value="${+p.p || 0}" style="max-width:110px"></td><td><input name="ncm${k}" value="${esc(p.ncm)}" style="max-width:130px"></td><td><input name="f${k}" type="number" step="0.01" min="0" value="${p.f ?? 1}" style="max-width:90px"></td><td>${produtos().length > 1 ? `<button type="button" class="lk" data-act="prodDel" data-id="${k}">Remover</button>` : ''}</td></tr>`).join('')}</tbody></table>
  <div class="fa"><button type="button" class="btn line" data-act="prodAdd">+ Produto</button><button class="btn ink">Salvar produtos</button></div></form>` : ''}
  <h3>Exportar</h3><div class="cb"><button class="btn line" data-act="csv" data-v="pdv">Baixar pontos (.csv)</button><button class="btn line" data-act="csv" data-v="ped">Baixar pedidos e visitas (.csv)</button></div>
  ${ad ? `<h3>Importar do painel antigo</h3><p class="lead">Use uma vez, com internet, com o arquivo pdvs-importacao.json. Pontos que já existem recebem só o histórico que faltar; nada é apagado.</p><label class="btn line" style="width:fit-content">Escolher arquivo<input type="file" id="impF" accept=".json,application/json" hidden></label><p class="pl" id="impMsg">${esc(impTxt)}</p>` : ''}` }

function vMais() {
  const ios = /iphone|ipad|ipod/i.test(navigator.userAgent), standalone = matchMedia('(display-mode: standalone)').matches || navigator.standalone;
  return `<h2>Mais</h2><div class="menu">
  <a href="#ranking">Ranking <span>quem mais compra e vende</span></a>
  <a href="#triagem">Triagem <span>${[...pdvs.values()].filter(p => p.status === 'verificar').length} a verificar</span></a>
  ${can.admin() ? `<a href="#notas">Notas fiscais <span>${peds.filter(o => o.nf && o.nf.st !== 'emitida').length} a emitir</span></a><a href="#equipe">Equipe <span>acessos dos vendedores</span></a>` : ''}
  <a href="#ajustes">Ajustes e exportar <span>regras e planilhas</span></a>
  ${!standalone && installEvt ? '<button data-act="install">Instalar app no celular <span>Android</span></button>' : ''}
  <button data-act="logout">Sair <span>${esc(me?.email || '')}</span></button></div>
  ${!standalone && ios ? `<div class="card" style="margin-top:16px;max-width:520px"><b>Instalar no iPhone</b><ol class="steps"><li>Abra este endereço no <b>Safari</b>.</li><li>Toque em <b>Compartilhar</b> (quadrado com seta pra cima).</li><li>Escolha <b>Adicionar à Tela de Início</b> e confirme.</li></ol></div>` : ''}
  <p class="pl" style="margin-top:18px">PDVs Seda de Favela · ${esc(PAPEIS[me?.papel] || '')}${navigator.onLine ? '' : ' · sem internet'}</p>` }

/* ---------- início: capa com os números de cada vendedor ---------- */
const nomeDe = email => { if (!email) return 'Sem vendedor'; const a = acessos.get(email); if (a?.nome) return a.nome; if (me && email === me.email) return me.nome;
  const o = peds.find(x => x.por === email && x.pn); if (o) return o.pn; for (const p of pdvs.values()) if (p.criadoPor === email && p.criadoPorNome) return p.criadoPorNome; return email.split('@')[0] };
function conquistador(p) { if (p.dono) return p.dono; if (p.criadoPor) return p.criadoPor; const f = M.get(p.id)?.ps.find(o => o.por); return f ? f.por : '' }
const conqD = p => (p.criadoPor && p.criado) || M.get(p.id)?.ps[0]?.d || p.criado || '';
function desdeDe(k) { const t = today(); return k === 'mes' ? t.slice(0, 8) + '01' : k === 'd90' ? addD(t, -89) : '0000-00-00' }
function numeros(email, k) { const de = desdeDe(k), mine = o => !email || o.por === email;
  const ps = peds.filter(o => mine(o) && o.d >= de), con = [...pdvs.values()].filter(p => p.status !== 'fechou' && (email ? conquistador(p) === email : conquistador(p)));
  const conP = con.filter(p => conqD(p) >= de);
  return { q: ps.reduce((a, o) => a + (+o.q || 0), 0), n: ps.length, v: ps.reduce((a, o) => a + (+o.v || 0), 0), pts: new Set(ps.map(o => o.pdv)).size,
    con, conP, at: con.filter(p => p.status === 'ativo').length, pro: con.filter(p => p.status === 'prospeccao').length } }
function vInicio() {
  const eq = can.admin() && iv === 'eq', em = eq ? '' : me.email, x = numeros(em, ip), pn = (me.nome || '').split(' ')[0];
  const PER = { mes: 'Este mês', d90: '90 dias', tudo: 'Desde o início' };
  const h0 = new Date().getHours(), oi = h0 < 12 ? 'Bom dia' : h0 < 18 ? 'Boa tarde' : 'Boa noite';
  const meus = x.con.slice().sort((a, b) => (conqD(b) > conqD(a) ? 1 : -1)).slice(0, 6);
  const rep = x.con.filter(p => p.status === 'ativo' && M.get(p.id).prox && M.get(p.id).dAte <= 3).sort((a, b) => M.get(a.id).dAte - M.get(b.id).dAte);
  // ranking da equipe no período
  const de = desdeDe(ip), rk = new Map(), add = (e, k, n) => { if (!e) return; const r = rk.get(e) || { q: 0, c: 0 }; r[k] += n; rk.set(e, r) };
  peds.filter(o => o.d >= de && o.por).forEach(o => add(o.por, 'q', +o.q || 0));
  [...pdvs.values()].forEach(p => { const c = conquistador(p); if (c && p.status !== 'fechou' && conqD(p) >= de) add(c, 'c', 1) });
  const rl = [...rk].sort((a, b) => b[1].q - a[1].q || b[1].c - a[1].c), mx = Math.max(1, ...rl.map(r => r[1].q)), pos = rl.findIndex(r => r[0] === me.email);
  let h = `<section class="capa"><div class="capa-t"><span class="pl">${oi}${eq ? '' : ','}</span><h2>${eq ? 'Números da equipe' : esc(pn || 'vendedor')}</h2>
   <p class="pl">${eq ? 'Tudo que a equipe vendeu e conquistou.' : pos >= 0 && rl.length > 1 ? `Você está em <b>${pos + 1}º</b> no ranking da equipe (${PER[ip].toLowerCase()}).` : 'Seus números na rua, atualizados a cada registro.'}</p></div>
   <div class="cta"><button class="btn mega" data-w data-act="newPdv"><span class="plus">+</span><span>Cadastrar novo PDV<small>ponto conquistado ou em prospecção</small></span></button>
   <button class="btn mega2" data-w data-act="newPed">Registrar pedido ou visita</button></div></section>
  <div class="chips">${can.admin() ? `<button class="chip ${!eq ? 'on' : ''}" data-act="iv" data-v="eu">Meus números</button><button class="chip ${eq ? 'on' : ''}" data-act="iv" data-v="eq">Equipe toda</button><span class="sep"></span>` : ''}${Object.entries(PER).map(([k, t]) => `<button class="chip ${ip === k ? 'on' : ''}" data-act="ip" data-v="${k}">${t}</button>`).join('')}</div>
  <div class="mets">
   <div class="met big"><span class="num">${nf(x.q)}</span><small>${esc(Us(x.q))} de seda vendidas</small><em>${x.n} ${x.n === 1 ? 'pedido' : 'pedidos'} em ${x.pts} ${x.pts === 1 ? 'ponto' : 'pontos'}</em></div>
   <div class="met big alt"><span class="num">${x.con.length}</span><small>estabelecimentos conquistados${eq ? '' : ' no seu nome'}</small><em>${x.conP.length ? `+${x.conP.length} ${ip === 'tudo' ? 'no total' : PER[ip].toLowerCase()}` : `nenhum novo ${ip === 'mes' ? 'este mês' : 'no período'}`}</em></div>
   <div class="met"><span class="num">${x.at}</span><small>conquistados ativos</small></div>
   <div class="met"><span class="num">${x.pro}</span><small>em prospecção</small></div>
   <div class="met"><span class="num">${x.v ? brl(x.v) : 'R$ 0'}</span><small>vendido${ip === 'tudo' ? '' : ' no período'}</small></div>
  </div>
  <div class="cols" style="margin-top:8px">
   <div class="rk"><h3>Ranking da equipe <span>${PER[ip]}</span></h3>${rl.length ? rl.slice(0, 8).map(([e, r], i) => `<div class="rr ${e === me.email ? 'me' : ''}" style="cursor:default"><i>${i + 1}</i><span class="n">${esc(nomeDe(e))}${e === me.email ? ' (você)' : ''}</span><span class="v">${nf(r.q)} ${esc(Us(r.q))} · ${r.c} novos</span><div class="tr"><div style="width:${r.q / mx * 100}%"></div></div></div>`).join('') : '<p class="pl">Ninguém registrou pedido nesse período ainda.</p>'}</div>
   <div class="rk"><h3>${eq ? 'Conquistas recentes' : 'Seus pontos'} <span>${x.con.length}</span></h3>${meus.length ? meus.map(p => `<div class="rr" data-act="open" data-id="${esc(p.id)}"><i>•</i><span class="n">${esc(p.nome)}</span><span class="v">${pill(p.status)}</span><span class="pl" style="grid-column:2/4">${esc(lugar(p))}${eq ? ' · ' + esc(nomeDe(conquistador(p))) : ''}</span></div>`).join('') + (x.con.length > 6 ? `<a class="lk" href="#pontos">Ver todos os pontos</a>` : '') : `<div class="empty" style="padding:16px">${eq ? 'Nenhum ponto tem vendedor definido ainda.' : 'Nenhum ponto no seu nome ainda. Cada ponto que você cadastrar ou fizer o primeiro pedido entra aqui.'}</div>`}
   ${rep.length ? `<h3>Pra repor até 3 dias <span>${rep.length}</span></h3>${rep.slice(0, 5).map(p => `<div class="rr" data-act="open" data-id="${esc(p.id)}"><i>!</i><span class="n">${esc(p.nome)}</span><span class="v">${M.get(p.id).dAte < 0 ? 'atrasado ' : ''}${rel(M.get(p.id).dAte)}</span></div>`).join('')}<a class="lk" href="#repor">Abrir reposição</a>` : ''}</div>
  </div>`;
  return h }

const V = { inicio: vInicio, notas: vNotas, repor: vRepor, pontos: vPontos, ranking: vRanking, bonus: vBonus, triagem: vTriagem, equipe: vEquipe, ajustes: vAjustes, mais: vMais };
const cur = () => { const h = location.hash.slice(1); return V[h] ? h : 'inicio' };
function render() {
  if (!me || $('#app').hidden) return; derive(); kpis(); const v = cur(); document.body.classList.toggle('v-inicio', v === 'inicio'); if (v === 'inicio' && !render.f) { render.f = 1; document.body.classList.add('first'); setTimeout(() => document.body.classList.remove('first'), 700) }
  const sub = ['ranking', 'triagem', 'equipe', 'ajustes', 'mais', 'notas'].includes(v);
  document.querySelectorAll('#tabs a').forEach(a => { const h = a.getAttribute('href'); a.classList.toggle('on', h === '#' + v || (sub && h === '#mais')) });
  const ae = document.activeElement, id = ae?.id, pos = ae?.selectionStart;
  $('#view').innerHTML = V[v]();
  if (id && $('#view #' + id)) { const e = $('#' + id); e.focus(); try { if (pos != null) e.setSelectionRange(pos, pos) } catch { } }
  if ($('#dlg').open && openId && pdvs.has(openId)) detail(openId);
}

/* ---------- janelas ---------- */
const dlg = $('#dlg');
function show(title, body) { $('#dlgIn').innerHTML = `<div class="dh"><h2>${title}</h2><button class="x" data-act="close" aria-label="Fechar">×</button></div><div class="db">${body}</div>`; if (!dlg.open) dlg.showModal() }
dlg.addEventListener('close', () => { openId = null; if (location.hash === '#novo') history.replaceState(null, '', '#inicio') });
function detail(id) { const p = pdvs.get(id); if (!p) return; openId = id; const s = M.get(id);
  show(esc(p.nome), `<div class="pl">${esc(lugar(p))}${p.endereco ? ' · ' + esc(p.endereco) : ''}</div>
  <div class="cb" style="margin:10px 0">${pill(p.status)} ${s.n ? tier(s.nivel) + ` <span class="pl">${s.pts} pts</span>` : ''} ${p.contato ? `<span class="pill">${esc(p.contato)}</span>` : ''}</div>
  <div class="cb"><button class="btn sm ink" data-w data-act="newPed" data-id="${esc(id)}">Registrar</button><button class="btn sm line" data-w data-act="edit" data-id="${esc(id)}">Editar</button>${wa(p)}${mapa(p)}</div>
  <div class="stats"><div><span class="num">${s.n}</span><small>pedidos</small></div><div><span class="num">${nf(s.qtd)}</span><small>${esc(U())}s no total</small></div>
  <div><span class="num">${s.giro ? nf(s.giro) : '—'}</span><small>giro/semana${s.giro && !s.medido ? ' (est.)' : ''}</small></div><div><span class="num">${s.prox ? fd(s.prox) : '—'}</span><small>${s.prox ? 'repor ' + rel(s.dAte) : 'sem previsão'}</small></div></div>
  ${s.receber ? `<div class="flag">A receber deste ponto: <b>${brl(s.receber)}</b></div>` : ''}
  ${(p.flags || []).length ? `<div class="flag" style="margin-top:8px">${p.flags.map(esc).join('<br>')} <button class="lk" data-w data-act="clrFlag" data-id="${esc(id)}">Resolvido</button></div>` : ''}
  ${p.redes ? `<p>Redes: ${esc(p.redes)}</p>` : ''}${p.doc ? `<p>CPF/CNPJ: ${esc(p.doc)}</p>` : ''}${p.obs ? `<p>${esc(p.obs)}</p>` : ''}
  <h3>Histórico</h3>${s.ev.length ? `<ul class="hist">${[...s.ev].reverse().map(o => { const mine = o.por === me.email || can.admin();
    return `<li><span><b>${fd(o.d)}/${o.d.slice(2, 4)}</b> · ${o.t === 'v' ? 'Visita' : `${nf(o.q)} ${esc(Us(+o.q))}${+o.v ? ' · ' + brl(o.v) : ''}`}${has(o.s) ? ` · sobra ${nf(o.s)}` : ''}${o.pn ? ` · <span class="pl">${esc(o.pn)}</span>` : ''}${o.o ? `<br><span class="pl">${esc(o.o)}</span>` : ''}</span>
    <span>${o.t !== 'v' ? `<button class="lk" data-act="rec" data-p="${esc(id)}" data-id="${esc(o.id)}">Comprovante</button>${o.nf ? `<span class="pill ${o.nf.st === 'emitida' ? 'p-ativo' : 'p-prospeccao'}">NF ${o.nf.st === 'emitida' ? 'emitida' : 'a emitir'}</span> ` : ''}` : ''}${o.t !== 'v' ? (o.pg === 'receber' ? `<button class="lk" data-w data-act="pago" data-id="${esc(o.id)}" data-p="${esc(id)}">Marcar pago</button>` : '<span class="pl">pago</span>') : ''}${mine && can.write() ? `<button class="lk" data-act="editPed" data-id="${esc(o.id)}" data-p="${esc(id)}">Editar</button><button class="lk" data-act="delPed" data-id="${esc(o.id)}" data-p="${esc(id)}">Apagar</button>` : ''}</span></li>` }).join('')}</ul>` : '<p class="pl">Nenhum registro ainda.</p>'}`) }

function pdvForm(id) { const p = id ? pdvs.get(id) : { status: 'prospeccao', tipo: 'Tabacaria' }; openId = null;
  const o = (v, t, c) => `<option value="${esc(v)}" ${c === v ? 'selected' : ''}>${esc(t)}</option>`, ind = p.indicadoPor && pdvs.get(p.indicadoPor);
  show(id ? 'Editar ponto' : 'Novo ponto de venda', `<form class="f" data-form="pdv" data-id="${esc(id || '')}">
  <label class="w">Nome do ponto<input name="nome" required value="${esc(p.nome)}" autocomplete="off"></label>
  <label>Status<select name="status">${Object.entries(ST).map(([k, v]) => o(k, v, p.status)).join('')}</select></label>
  <label>Tipo<select name="tipo">${TIPOS.map(t => o(t, t, p.tipo)).join('')}</select></label>
  <label>WhatsApp / telefone<input name="contato" type="tel" inputmode="tel" value="${esc(p.contato)}"></label>
  <label>Bairro<input name="bairro" value="${esc(p.bairro)}"></label>
  <label>Cidade<input name="cidade" value="${esc(p.cidade)}" list="cidList"></label>
  <label>UF<input name="uf" maxlength="2" value="${esc(p.uf)}"></label>
  <label class="w">Endereço<input name="endereco" value="${esc(p.endereco)}"></label>
  <label>Instagram / redes<input name="redes" value="${esc(p.redes)}"></label>
  <label>CPF / CNPJ<input name="doc" inputmode="numeric" value="${esc(p.doc)}"><small>Obrigatório para nota fiscal</small></label>
  <label class="w">Razão social / nome completo<input name="razao" value="${esc(p.razao)}"><small>Como vai sair na nota. Vazio: usa o nome do ponto</small></label>
  <label>Inscrição estadual<input name="ie" value="${esc(p.ie)}" placeholder="Isento, se não tiver"></label>
  <label>CEP<input name="cep" inputmode="numeric" value="${esc(p.cep)}"></label>
  <label>E-mail<input name="email" type="email" value="${esc(p.email)}"></label>
  <label>Ciclo fixo de reposição (dias)<input name="ciclo" type="number" inputmode="numeric" min="1" value="${esc(p.ciclo || '')}"><small>Vazio: o app calcula</small></label>
  <label>Retornar na prospecção em<input name="proxContato" type="date" value="${esc(p.proxContato || '')}"></label>
  <label class="w">Indicado por<input name="ind" list="pdvList" value="${esc(ind ? lbl(ind) : '')}" autocomplete="off"><small>Outro ponto que indicou este. Gera bônus pra quem indicou.</small></label>
  ${can.admin() ? `<label class="w">Conquistado por<select name="dono"><option value="">${p.criadoPor || p.dono ? '' : 'Ninguém definido'}</option>${[...new Set([me.email, ...acessos.keys(), ...(p.dono ? [p.dono] : []), ...(p.criadoPor ? [p.criadoPor] : [])])].map(e => `<option value="${esc(e)}" ${(p.dono || p.criadoPor) === e ? 'selected' : ''}>${esc(nomeDe(e))}</option>`).join('')}</select><small>Vendedor que leva o ponto nas métricas do Início</small></label>` : ''}
  <label class="w">Observações<textarea name="obs" rows="3">${esc(p.obs)}</textarea></label>
  <div class="fa w">${id && can.admin() ? `<button type="button" class="btn del" data-act="delPdv" data-id="${esc(id)}">Excluir ponto</button>` : ''}<button type="button" class="btn line" data-act="close">Cancelar</button><button class="btn ink">Salvar</button></div></form>
  <datalist id="cidList">${[...new Set([...pdvs.values()].map(x => x.cidade).filter(Boolean))].sort().map(c => `<option value="${esc(c)}">`).join('')}</datalist>
  <datalist id="pdvList">${[...pdvs.values()].map(x => `<option value="${esc(lbl(x))}">`).join('')}</datalist>`) }

/* formulário de campo: pedido ou visita, feito para o polegar */
function pedForm(pid, oid, ppid) {
  const p0 = pdvs.get(pid || ppid), o = oid ? (p0?.hist || []).find(x => x.id === oid) : { t: 'p', d: today(), q: '', pg: 'pago' };
  if (!o) return; openId = null;
  const st = { pdv: p0?.id || '', t: o.t || 'p' };
  show(oid ? 'Editar registro' : 'Registrar', `<form class="f" data-form="ped" data-id="${esc(oid || '')}">
  <div class="w seg" role="group"><button type="button" data-t="p">Pedido</button><button type="button" data-t="v">Só visita</button></div>
  <div class="w" id="pdvBox"></div>
  <div class="w tp"><b style="font-size:14px">Produtos</b><div id="itBox"></div></div>
  <label>Sobra encontrada no ponto<div class="step"><button type="button" data-inc="s" data-d="-1">−</button><input name="s" type="number" inputmode="decimal" min="0" step="0.5" value="${esc(o.s ?? '')}" placeholder="não contei"><button type="button" data-inc="s" data-d="1">+</button></div><small>Quantas ${esc(U())}s ainda tinham lá. Mede o giro.</small></label>
  <label class="tp">Desconto (R$)<input name="ds" type="number" min="0" step="0.01" inputmode="decimal" value="${esc(o.ds || '')}" placeholder="0,00"></label>
  <label class="tp">Forma de pagamento<select name="fp">${FP.map(x => `<option ${(o.fp || 'PIX') === x ? 'selected' : ''}>${x}</option>`).join('')}</select></label>
  <div class="w tp"><div class="seg" id="pgSeg"><button type="button" data-pg="pago">Pago</button><button type="button" data-pg="receber">A receber</button></div></div>
  <label class="tp" id="vencL">Vencimento<input name="venc" type="date" value="${esc(o.venc || addD(today(), 7))}"></label>
  <div class="w tp tot" id="totBox"></div>
  <label>Data<input name="d" type="date" required value="${esc(o.d)}"></label>
  <label>Observação<input name="o" value="${esc(o.o)}" placeholder="Opcional"></label>
  <div class="fa w"><button class="btn ink" style="flex:1;min-height:54px;font-size:17px">Salvar</button></div></form>`);
  const f = $('#dlgIn form'); f.dataset.pg = o.pg || 'pago'; f.dataset.ppid = ppid || '';
  const its = clone(itensDe(o)); if (!its.length) { const p0 = produtos()[0]; its.push({ c: p0.c, d: p0.d, un: p0.un, ncm: p0.ncm, q: 0, pu: +p0.p || 0 }) }
  f._its = its;
  const paintIts = () => {
    const ps = produtos();
    $('#itBox').innerHTML = its.map((i, k) => `<div class="itl"><select data-itp="${k}" aria-label="Produto">${ps.map(p => `<option value="${esc(p.c)}" ${p.c === i.c ? 'selected' : ''}>${esc(p.d)}</option>`).join('')}${ps.some(p => p.c === i.c) ? '' : `<option value="${esc(i.c)}" selected>${esc(i.d)}</option>`}</select>
      <div class="step"><button type="button" data-itd="${k}" data-d="-1">−</button><input data-itq="${k}" type="number" inputmode="decimal" min="0" step="1" value="${i.q || ''}" placeholder="0"><button type="button" data-itd="${k}" data-d="1">+</button></div>
      <label class="pu">R$ unid.<input data-itu="${k}" type="number" inputmode="decimal" min="0" step="0.01" value="${i.pu ? (+i.pu).toFixed(2) : ''}" placeholder="0,00"></label>
      <span class="lt">${brl((+i.q || 0) * (+i.pu || 0))}</span>${its.length > 1 ? `<button type="button" class="lk" data-itx="${k}">Remover</button>` : ''}</div>`).join('') + `<button type="button" class="btn sm line" data-itadd>+ Outro produto</button>`;
    paintTot() };
  const paintTot = () => { const sub = its.reduce((a, i) => a + (+i.q || 0) * (+i.pu || 0), 0), ds = +f.elements.ds.value || 0;
    $('#totBox').innerHTML = `<span>Total</span><b>${brl(Math.max(0, sub - ds))}</b>`;
    f.querySelectorAll('.itl .lt').forEach((e, k) => e.textContent = brl((+its[k].q || 0) * (+its[k].pu || 0))) };
  f.addEventListener('input', e => { const t = e.target;
    if (t.dataset.itq != null) its[+t.dataset.itq].q = +t.value || 0;
    if (t.dataset.itu != null) its[+t.dataset.itu].pu = +t.value || 0;
    if (t.name === 'ds' || t.dataset.itq != null || t.dataset.itu != null) paintTot() });
  f.addEventListener('change', e => { const t = e.target; if (t.dataset.itp != null) { const p = prodDe(t.value), i = its[+t.dataset.itp]; Object.assign(i, { c: p.c, d: p.d, un: p.un, ncm: p.ncm, pu: +p.p || i.pu }); paintIts() } });
  const paint = () => {
    f.dataset.t = st.t; f.dataset.pdv = st.pdv;
    f.querySelectorAll('[data-t]').forEach(b => b.classList.toggle('on', b.dataset.t === st.t));
    f.querySelectorAll('.tp').forEach(x => x.hidden = st.t === 'v');
    f.querySelectorAll('[data-pg]').forEach(b => b.classList.toggle('on', b.dataset.pg === f.dataset.pg));
    $('#vencL').hidden = st.t === 'v' || f.dataset.pg !== 'receber';
    const p = pdvs.get(st.pdv), box = $('#pdvBox');
    if (p) box.innerHTML = `<div class="chosen"><div><b>${esc(p.nome)}</b><div class="pl">${esc(lugar(p))}</div></div>${oid ? '' : '<button type="button" class="btn sm line" id="pdvTroca">Trocar</button>'}</div>`;
    else { box.innerHTML = `<label>Ponto de venda<input id="pdvQ" type="search" placeholder="Digite o nome, bairro ou cidade" autocomplete="off"></label><div class="pick" id="pdvRes"></div>`; const q = $('#pdvQ'); q.addEventListener('input', find); find(); setTimeout(() => q.focus(), 50) }
    $('#pdvTroca')?.addEventListener('click', () => { st.pdv = ''; paint() });
  };
  const find = () => { const q = ($('#pdvQ')?.value || '').toLowerCase().trim(), all = [...pdvs.values()].filter(p => p.status !== 'fechou');
    const l = (q ? all.filter(p => [p.nome, p.bairro, p.cidade].join(' ').toLowerCase().includes(q)) : all.filter(p => p.status === 'ativo').sort((a, b) => (M.get(a.id).dAte ?? 1e9) - (M.get(b.id).dAte ?? 1e9))).slice(0, 8);
    $('#pdvRes').innerHTML = l.length ? l.map(p => `<button type="button" data-pick="${esc(p.id)}">${esc(p.nome)}<small>${esc(lugar(p))} · ${esc(ST[p.status])}</small></button>`).join('') : '<p class="pl">Nenhum ponto encontrado. Cadastre em + Ponto.</p>' };
  f.addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    if (b.dataset.t) { st.t = b.dataset.t; paint() }
    if (b.dataset.pg) { f.dataset.pg = b.dataset.pg; paint() }
    if (b.dataset.pick) { st.pdv = b.dataset.pick; paint() }
    if (b.dataset.itd != null) { const i = its[+b.dataset.itd]; i.q = Math.max(0, (+i.q || 0) + (+b.dataset.d)); paintIts(); return }
    if (b.dataset.itx != null) { its.splice(+b.dataset.itx, 1); paintIts(); return }
    if (b.dataset.itadd != null) { const p0 = produtos()[0]; its.push({ c: p0.c, d: p0.d, un: p0.un, ncm: p0.ncm, q: 0, pu: +p0.p || 0 }); paintIts(); return }
    if (b.dataset.inc) { const i = f.elements[b.dataset.inc]; i.value = Math.max(0, (+i.value || 0) + (+b.dataset.d)); i.dispatchEvent(new Event('input', { bubbles: true })) }
  });
  paint(); paintIts();
}

/* comprovante de venda (pedido) */
function recHTML(p, o) { const e = emp(), its = itensDe(o), sub = subtotal(o), nfo = o.nf;
  const L = (k, v) => v ? `<div><span>${k}</span>${esc(v)}</div>` : '';
  return `<div class="rec" id="rec"><div class="rh"><img src="logo.png" alt=""><div><b>PEDIDO DE VENDA</b><span>Nº ${esc(o.n || o.id)}</span><span>${brD(o.d)}</span></div></div>
  <div class="rb"><h4>Empresa</h4>${L('', e.razao || 'Seda de Favela')}${L('CNPJ/CPF', e.doc)}${L('IE', e.ie)}${L('', [e.endereco, e.bairro].filter(Boolean).join(' - '))}${L('', [e.cidade, e.uf].filter(Boolean).join('/') + (e.cep ? ' · CEP ' + e.cep : ''))}${L('Contato', [e.tel, e.email].filter(Boolean).join(' · '))}</div>
  <div class="rb"><h4>Cliente</h4>${L('', p.razao || p.nome)}${p.razao && p.razao !== p.nome ? L('Ponto', p.nome) : ''}${L('CPF/CNPJ', p.doc)}${L('IE', p.ie)}${L('', p.endereco)}${L('', [p.bairro, [p.cidade, p.uf].filter(Boolean).join('/')].filter(Boolean).join(' · ') + (p.cep ? ' · CEP ' + p.cep : ''))}${L('Contato', p.contato)}</div>
  <table class="rt"><thead><tr><th>Produto</th><th class="r">Qtd</th><th class="r">Unit.</th><th class="r">Total</th></tr></thead><tbody>${its.map(i => `<tr><td>${esc(i.d)}<small>${esc([i.c, i.ncm && 'NCM ' + i.ncm].filter(Boolean).join(' · '))}</small></td><td class="r">${nf(i.q)} ${esc(i.un || '')}</td><td class="r">${brl(i.pu)}</td><td class="r">${brl(i.q * i.pu)}</td></tr>`).join('')}</tbody></table>
  <div class="rs">${o.ds ? `<div><span>Subtotal</span>${brl(sub)}</div><div><span>Desconto</span>- ${brl(o.ds)}</div>` : ''}<div class="big"><span>Total</span>${brl(o.v)}</div></div>
  <div class="rb"><h4>Pagamento</h4>${L('Forma', o.fp)}${L('Situação', o.pg === 'receber' ? 'A receber' + (o.venc ? ' até ' + brD(o.venc) : '') : 'Pago')}${o.pg === 'receber' && e.pix ? L('Chave PIX', e.pix) : ''}</div>
  ${o.o ? `<div class="rb"><h4>Observação</h4><div>${esc(o.o)}</div></div>` : ''}
  <div class="rf">Vendedor: ${esc(o.pn || o.por || '')}${nfo ? ` · NF-e: ${nfo.st === 'emitida' ? 'emitida nº ' + esc(nfo.num || '') : 'a emitir'}` : ''}<br>${esc(e.rodape || 'Documento de controle interno, sem valor fiscal. A nota fiscal eletrônica, quando emitida, é enviada separadamente.')}</div></div>` }
function recibo(pid, oid) { const p = pdvs.get(pid), o = (p?.hist || []).find(x => x.id === oid); if (!p || !o) return; openId = null;
  const falta = o.nf && o.nf.st !== 'emitida' ? faltaNF(p) : [], dg = String(p.contato || '').replace(/\D/g, '');
  show('Pedido salvo', `${recHTML(p, o)}
  ${falta.length ? `<div class="flag noprint" style="margin-top:12px">Para a nota fiscal ainda falta: <b>${falta.map(esc).join(', ')}</b>. <button class="lk" data-act="edit" data-id="${esc(pid)}">Completar cliente</button></div>` : ''}
  <div class="cb noprint" style="margin-top:14px"><button class="btn sun" data-act="recShare" data-p="${esc(pid)}" data-id="${esc(oid)}">Enviar imagem</button>${dg.length >= 10 ? `<button class="btn line" data-act="recWa" data-p="${esc(pid)}" data-id="${esc(oid)}">WhatsApp (texto)</button>` : ''}<button class="btn line" data-act="recPrint">Imprimir / PDF</button>${o.nf && o.nf.st !== 'emitida' ? `<button class="btn line" data-act="notaCopy" data-p="${esc(pid)}" data-id="${esc(oid)}">Copiar dados p/ nota</button>` : ''}<button class="btn line" data-act="open" data-id="${esc(pid)}">Ver ponto</button></div>`) }
function recTexto(p, o) { const e = emp(), its = itensDe(o);
  return [`*PEDIDO DE VENDA Nº ${o.n || o.id}*`, `${e.razao || 'Seda de Favela'}${e.doc ? ' · ' + e.doc : ''}`, `Data: ${brD(o.d)}`, `Cliente: ${p.razao || p.nome}${p.doc ? ' · ' + p.doc : ''}`, '', ...its.map(i => `• ${nf(i.q)} ${i.un || ''} ${i.d} x ${brl(i.pu)} = ${brl(i.q * i.pu)}`), o.ds ? `Desconto: - ${brl(o.ds)}` : '', `*Total: ${brl(o.v)}*`, `Pagamento: ${o.fp || ''} · ${o.pg === 'receber' ? 'a receber' + (o.venc ? ' até ' + brD(o.venc) : '') : 'pago'}`, o.pg === 'receber' && e.pix ? `PIX: ${e.pix}` : '', `Vendedor: ${o.pn || ''}`, '', '_Documento sem valor fiscal._'].filter(x => x !== '').join('\n') }
function notaTexto(p, o) { const its = itensDe(o), L = [];
  L.push('DESTINATÁRIO', `CNPJ/CPF: ${p.doc || '(falta)'}`, `Nome/Razão social: ${p.razao || p.nome}`, `Inscrição estadual: ${p.ie || 'Isento/não contribuinte'}`, `Endereço: ${p.endereco || '(falta)'}`, `Bairro: ${p.bairro || ''}`, `CEP: ${p.cep || '(falta)'}`, `Município/UF: ${p.cidade || ''}/${p.uf || ''}`, `Telefone: ${p.contato || ''}`, `E-mail: ${p.email || ''}`, '', 'PRODUTOS');
  its.forEach((i, k) => L.push(`${k + 1}) ${i.d}`, `   Código: ${i.c || ''} · NCM: ${i.ncm || ''} · Unidade: ${i.un || ''}`, `   Quantidade: ${String(i.q).replace('.', ',')} · Valor unitário: ${(+i.pu).toFixed(2).replace('.', ',')} · Valor total: ${(i.q * i.pu).toFixed(2).replace('.', ',')}`));
  L.push('', `Desconto: ${(+o.ds || 0).toFixed(2).replace('.', ',')}`, `VALOR TOTAL DA NOTA: ${(+o.v).toFixed(2).replace('.', ',')}`, '', 'PAGAMENTO', `Forma: ${o.fp || ''} · ${o.pg === 'receber' ? 'a prazo, vencimento ' + brD(o.venc) : 'à vista'}`, '', 'INFORMAÇÕES COMPLEMENTARES', `Pedido ${o.n || o.id} de ${brD(o.d)}. Vendedor: ${o.pn || ''}.`);
  return L.join('\n') }
async function recImagem(p, o) {
  const W = 1080, P = 64, c = document.createElement('canvas'), x = c.getContext('2d'), e = emp(), its = itensDe(o), rows = [];
  const T = (t, f, col = '#1a1714', a = 'left', gap = 12) => rows.push({ t: String(t ?? ''), f, col, a, gap });
  T('PEDIDO DE VENDA', '800 56px "Barlow Condensed"', '#8a0b0b', 'left', 6); T('Nº ' + (o.n || o.id) + '  ·  ' + brD(o.d), '600 30px Barlow', '#1a1714', 'left', 30);
  T('EMPRESA', '700 24px Barlow', '#8a8178', 'left', 4); T(e.razao || 'Seda de Favela', '600 30px Barlow'); if (e.doc) T('CNPJ/CPF ' + e.doc + (e.ie ? '  ·  IE ' + e.ie : ''), '400 26px Barlow'); if (e.tel) T(e.tel, '400 26px Barlow', '#1a1714', 'left', 26);
  T('CLIENTE', '700 24px Barlow', '#8a8178', 'left', 4); T(p.razao || p.nome, '600 30px Barlow'); if (p.doc) T('CPF/CNPJ ' + p.doc, '400 26px Barlow'); const end = [p.endereco, p.bairro, [p.cidade, p.uf].filter(Boolean).join('/')].filter(Boolean).join(' · '); if (end) T(end, '400 24px Barlow', '#1a1714', 'left', 26);
  T('PRODUTOS', '700 24px Barlow', '#8a8178', 'left', 8);
  its.forEach(i => { T(i.d, '600 28px Barlow', '#1a1714', 'left', 2); T(`${nf(i.q)} ${i.un || ''} x ${brl(i.pu)} = ${brl(i.q * i.pu)}`, '400 26px Barlow', '#1a1714', 'left', 14) });
  if (o.ds) T('Desconto: - ' + brl(o.ds), '400 26px Barlow');
  T('TOTAL ' + brl(o.v), '800 52px "Barlow Condensed"', '#1a1714', 'left', 20);
  T(`Pagamento: ${o.fp || ''} · ${o.pg === 'receber' ? 'a receber' + (o.venc ? ' até ' + brD(o.venc) : '') : 'pago'}`, '600 26px Barlow'); if (o.pg === 'receber' && e.pix) T('PIX: ' + e.pix, '600 26px Barlow');
  T('Vendedor: ' + (o.pn || ''), '400 24px Barlow', '#1a1714', 'left', 28); T('Documento sem valor fiscal.', 'italic 400 22px Barlow', '#8a8178');
  let h = P + 200; x.font = '10px Barlow'; for (const r of rows) h += parseInt(r.f.match(/(\d+)px/)[1]) * 1.25 + r.gap; c.width = W; c.height = h + P;
  x.fillStyle = '#fff'; x.fillRect(0, 0, W, c.height); x.fillStyle = '#8a0b0b'; x.fillRect(0, 0, W, 14);
  try { await document.fonts.ready; const img = new Image(); img.src = 'logo.png'; await img.decode(); const s = 170 / img.height; x.drawImage(img, W - P - img.width * s, P - 10, img.width * s, 170) } catch { }
  let y = P + 10; for (const r of rows) { const sz = parseInt(r.f.match(/(\d+)px/)[1]); x.font = r.f; x.fillStyle = r.col; x.textBaseline = 'top'; let t = r.t; while (x.measureText(t).width > W - 2 * P - (y < P + 180 ? 200 : 0) && t.length > 4) t = t.slice(0, -2); if (t !== r.t) t = t.slice(0, -1) + '…'; x.fillText(t, P, y); y += sz * 1.25 + r.gap }
  return new Promise(r => c.toBlob(r, 'image/png')) }

function bonForm(id) { const p = pdvs.get(id), s = M.get(id); openId = null;
  show('Registrar bonificação', `<form class="f" data-form="bon" data-id="${esc(id)}"><p class="w"><b>${esc(p.nome)}</b> está no nível ${tier(s.nivel)} com ${s.pts} pts.</p>
  <label class="w">O que foi entregue<input name="desc" required value="${esc(cfg.niveis[s.nivel].premio)}"></label><label>Data<input name="data" type="date" value="${today()}"></label>
  <div class="fa w"><button type="button" class="btn line" data-act="close">Cancelar</button><button class="btn ink">Registrar</button></div></form>`) }

/* ---------- gravação ---------- */
function toast(m, u) { $('#tMsg').textContent = m; const b = $('#tBtn'); undo = u || null; b.hidden = !u; const t = $('#toast'); t.classList.add('on'); clearTimeout(toast.t); toast.t = setTimeout(() => { t.classList.remove('on'); undo = null }, u ? 7000 : 3200) }
$('#tBtn').onclick = () => { const u = undo; $('#toast').classList.remove('on'); undo = null; if (u) u() };
const errMsg = e => e?.code === 'permission-denied' ? 'Sem permissão para essa alteração. Ela foi desfeita.' : 'Não salvou (' + (e?.code || 'erro') + '). Tente de novo.';
// Não espera o servidor: sem sinal, a promessa só resolve quando a conexão voltar. A tela já mostra a mudança na hora.
function fire(p, ok) { p.catch(e => toast(errMsg(e))); if (ok) toast(ok + (navigator.onLine ? '' : ' Sobe quando tiver sinal.')) }
const pref = id => doc(db, 'pdvs', id);
const byLbl = v => [...pdvs.values()].find(p => lbl(p) === v) || [...pdvs.values()].find(p => p.nome.toLowerCase() === String(v).trim().toLowerCase());
const stripId = p => { const { id, ...r } = p; return r };

document.addEventListener('submit', async e => {
  const f = e.target; if (f.id === 'loginF') return; e.preventDefault(); const v = Object.fromEntries(new FormData(f));
  if (f.id === 'cfgF') { const c = { ...cfg, unidade: v.unidade.trim() || 'caixa', preco: +v.preco || 0, ciclo: +v.ciclo || 15, janela: +v.janela || 90, ptsCaixa: +v.ptsCaixa || 0, ptsPontual: +v.ptsPontual || 0, ptsIndicacao: +v.ptsIndicacao || 0,
      niveis: cfg.niveis.map((_, i) => ({ nome: v['n' + i].trim(), min: i ? +v['m' + i] || 0 : 0, premio: v['p' + i].trim() })) };
    for (let i = 1; i < 4; i++) if (c.niveis[i].min <= c.niveis[i - 1].min) return toast('Cada nível precisa de mais pontos que o anterior.');
    return fire(setDoc(doc(db, 'config', 'geral'), c), 'Ajustes salvos') }
  if (f.id === 'teamF') return addMember(v, f);
  if (f.id === 'empF') { const e = {}; for (const k of ['razao', 'doc', 'ie', 'endereco', 'bairro', 'cidade', 'uf', 'cep', 'tel', 'email', 'pix', 'rodape']) e[k] = (v[k] || '').trim(); e.uf = e.uf.toUpperCase();
    return fire(setDoc(doc(db, 'config', 'geral'), { ...cfg, empresa: e, controlaNF: !!v.controlaNF }), 'Dados da empresa salvos') }
  if (f.id === 'prodF') { const l = produtos().map((_, k) => ({ c: v['c' + k].trim(), d: v['d' + k].trim(), un: (v['un' + k] || 'UN').trim().toUpperCase(), p: +v['p' + k] || 0, ncm: (v['ncm' + k] || '').trim(), f: v['f' + k] === '' ? 1 : +v['f' + k] }));
    if (new Set(l.map(x => x.c)).size !== l.length) return toast('Cada produto precisa de um código diferente.');
    return fire(setDoc(doc(db, 'config', 'geral'), { ...cfg, produtos: l }), 'Produtos salvos') }
  if (f.dataset.form === 'nf') { const p = pdvs.get(f.dataset.p); fire(updateDoc(pref(p.id), { hist: p.hist.map(x => x.id === f.dataset.id ? { ...x, nf: { st: 'emitida', num: v.num.trim(), data: v.data, chave: v.chave.trim() } } : x) }), 'NF-e marcada como emitida'); dlg.close(); return }
  const t = f.dataset.form, id = f.dataset.id;
  if (t === 'pdv') { const ind = v.ind ? byLbl(v.ind) : null;
    const d = { nome: v.nome.trim(), status: v.status, tipo: v.tipo, contato: v.contato.trim(), bairro: v.bairro.trim(), cidade: v.cidade.trim(), uf: v.uf.trim().toUpperCase(), endereco: v.endereco.trim(), redes: v.redes.trim(), doc: v.doc.trim(), razao: v.razao.trim(), ie: v.ie.trim(), cep: v.cep.trim(), email: v.email.trim(), ciclo: +v.ciclo || null, proxContato: v.proxContato || null, indicadoPor: ind && ind.id !== id ? ind.id : null, obs: v.obs.trim(), atualizado: today(), atualizadoPor: me.email };
    if ('dono' in v) d.dono = v.dono || null;
    if (id) { fire(updateDoc(pref(id), d), 'Ponto atualizado'); detail(id) }
    else { const r = doc(collection(db, 'pdvs')); fire(setDoc(r, { ...d, hist: [], flags: [], criado: today(), criadoPor: me.email, criadoPorNome: me.nome }), 'Ponto cadastrado'); dlg.close() }
    return }
  if (t === 'ped') { const p = pdvs.get(f.dataset.pdv); if (!p) return toast('Escolha o ponto de venda.');
    const tv = f.dataset.t === 'v', its = (f._its || []).filter(i => +i.q > 0).map(i => ({ c: i.c, d: i.d, un: i.un || 'UN', ncm: i.ncm || '', q: +i.q, pu: +i.pu || 0 }));
    const q = its.reduce((a, i) => a + i.q * (prodDe(i.c)?.f ?? 1), 0), ds = +v.ds || 0, tot = Math.max(0, its.reduce((a, i) => a + i.q * i.pu, 0) - ds);
    if (!tv && !its.length) return toast('Coloque a quantidade de pelo menos um produto.');
    if (tv && !has(v.s) && !v.o.trim()) return toast('Na visita, anote a sobra ou uma observação.');
    const old = id ? (p.hist || []).find(x => x.id === id) : null;
    const en = { id: id || rid(), t: tv ? 'v' : 'p', d: v.d, q: tv ? 0 : q, v: tv ? 0 : tot, s: has(v.s) ? +v.s : null, pg: tv ? null : f.dataset.pg, o: v.o.trim(), por: old?.por || me.email, pn: old?.pn || me.nome, em: old?.em || Date.now() };
    if (!tv) Object.assign(en, { n: old?.n || numPedido(v.d), it: its, ds, fp: v.fp, venc: f.dataset.pg === 'receber' ? v.venc : null, nf: old?.nf || (cfg.controlaNF === false ? null : { st: 'pendente' }) });
    if (old) fire(updateDoc(pref(p.id), { hist: (p.hist || []).map(x => x.id === id ? en : x) }), 'Registro atualizado');
    else { const up = { hist: arrayUnion(en), atualizado: today() }; let msg = tv ? 'Visita registrada' : 'Pedido salvo';
      if (!tv && p.status !== 'ativo') { up.status = 'ativo'; msg += `. ${p.nome} agora é Ativo` }
      fire(updateDoc(pref(p.id), up), msg) }
    if (location.hash === '#novo') history.replaceState(null, '', '#inicio');
    setTimeout(() => (!tv && !old) ? recibo(p.id, en.id) : detail(p.id), 30); return }
  if (t === 'bon') { fire(addDoc(collection(db, 'bonus'), { pdv: id, desc: v.desc.trim(), data: v.data || today(), por: me.email }), 'Bonificação registrada'); dlg.close() }
});

async function addMember(v, f) {
  const email = v.email.trim().toLowerCase(); if (!navigator.onLine) return toast('Para dar acesso precisa de internet.');
  if (email === ADMIN_EMAIL.toLowerCase()) return toast('Esse e-mail já é a administradora.');
  try {
    await setDoc(doc(db, 'acessos', email), { nome: v.nome.trim(), papel: v.papel, ativo: true, criado: today(), criadoPor: me.email });
    // cria a conta numa instância separada, para a administradora não ser deslogada
    const sec = initializeApp(firebaseConfig, 'conta-' + Date.now()), sa = getAuth(sec);
    try { await createUserWithEmailAndPassword(sa, email, v.senha); toast(`Acesso criado. Passe para ${v.nome.trim()}: e-mail ${email} e a senha inicial.`) }
    catch (x) { toast(x.code === 'auth/email-already-in-use' ? 'Esse e-mail já tinha conta: o acesso foi liberado. A pessoa entra com a senha que já usa.' : 'Acesso liberado, mas a conta não foi criada (' + x.code + ').') }
    finally { try { await signOut(sa) } catch { } }
    f.reset();
  } catch (x) { toast(errMsg(x)) }
}

function download(name, text) { const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob(['﻿' + text], { type: 'text/csv;charset=utf-8' })); a.download = name; document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove() }, 500) }

document.addEventListener('click', e => {
  const g = e.target.closest('[data-go]'); if (g) { if (g.dataset.st) F = { ...F, st: g.dataset.st }; location.hash = g.dataset.go; return }
  const a = e.target.closest('[data-act]'); if (!a || a.tagName === 'SELECT') return; const { act, id, st, v } = a.dataset;
  if (act === 'close') return dlg.close();
  if (act === 'open') return detail(id);
  if (act === 'logout') return signOut(auth);
  if (act === 'install') { installEvt?.prompt(); installEvt = null; return }
  if (act === 'per') { per = +v; return render() }
  if (act === 'rcid') { rcid = v; return render() }
  if (act === 'ip') { ip = v; return render() }
  if (act === 'iv') { iv = v; return render() }
  if (act === 'skip') { skip.add(id); return render() }
  if (act === 'unskip') { skip.clear(); return render() }
  if (act === 'recWa') { const p = pdvs.get(a.dataset.p), o = p.hist.find(x => x.id === id), d = String(p.contato).replace(/\D/g, ''); window.open(`https://wa.me/${d.length <= 11 ? '55' + d : d}?text=${encodeURIComponent(recTexto(p, o))}`, '_blank'); return }
  if (act === 'recShare') { const p = pdvs.get(a.dataset.p), o = p.hist.find(x => x.id === id);
    recImagem(p, o).then(async b => { const file = new File([b], `pedido-${o.n || o.id}.png`, { type: 'image/png' });
      if (navigator.canShare && navigator.canShare({ files: [file] })) { try { await navigator.share({ files: [file], title: 'Pedido ' + (o.n || ''), text: recTexto(p, o) }) } catch { } }
      else { const u = URL.createObjectURL(b), l = document.createElement('a'); l.href = u; l.download = file.name; document.body.appendChild(l); l.click(); setTimeout(() => { URL.revokeObjectURL(u); l.remove() }, 500); toast('Imagem do pedido baixada.') } }); return }
  if (act === 'notaCopy') { const p = pdvs.get(a.dataset.p), o = p.hist.find(x => x.id === id); navigator.clipboard.writeText(notaTexto(p, o)).then(() => toast('Dados da nota copiados. Cole no bloco de notas ou no WhatsApp para ir conferindo.')).catch(() => toast('O navegador bloqueou a cópia.')); return }
  if (act === 'recPrint') { document.body.classList.add('printing'); setTimeout(() => { window.print(); document.body.classList.remove('printing') }, 50); return }
  if (act === 'rec') return recibo(a.dataset.p, id);
  if (act === 'nfOk' && can.admin()) return nfForm(a.dataset.p, id);
  if (act === 'csvNF' && can.admin()) return csvNF();
  if (act === 'prodAdd' && can.admin()) { const l = clone(produtos()); l.push({ c: 'NOVO-' + (l.length + 1), d: 'Novo produto', un: 'UN', p: 0, ncm: '', f: 0 }); return fire(setDoc(doc(db, 'config', 'geral'), { ...cfg, produtos: l }), 'Produto adicionado') }
  if (act === 'prodDel' && can.admin()) { const l = clone(produtos()); l.splice(+id, 1); return fire(setDoc(doc(db, 'config', 'geral'), { ...cfg, produtos: l }), 'Produto removido') }
  if (act === 'csv') { const q = x => `"${String(x ?? '').replace(/"/g, '""')}"`; let rows;
    if (v === 'pdv') rows = [['Nome', 'Status', 'Tipo', 'Contato', 'Bairro', 'Cidade', 'UF', 'Endereço', 'Redes', 'CPF/CNPJ', 'Pedidos', 'Total', 'Último pedido', 'Próxima reposição', 'Giro/semana', 'Pontos', 'Nível', 'Obs'], ...[...pdvs.values()].map(p => { const s = M.get(p.id); return [p.nome, ST[p.status], p.tipo, p.contato, p.bairro, p.cidade, p.uf, p.endereco, p.redes, p.doc, s.n, s.qtd, s.last?.d || '', s.prox || '', s.giro ? nf(s.giro) : '', s.pts, cfg.niveis[s.nivel].nome, p.obs] })];
    else rows = [['Pedido', 'Data', 'Tipo', 'Ponto', 'Cidade', 'Quantidade', 'Valor', 'Sobra', 'Pagamento', 'Registrado por', 'Obs'], ...evs.slice().sort(byD).map(o => { const p = pdvs.get(o.pdv) || {}; return [o.n || '', o.d, o.t === 'v' ? 'Visita' : 'Pedido', p.nome, p.cidade, o.q, o.v, o.s ?? '', o.pg || '', o.pn || o.por || '', o.o] })];
    return download(`${v === 'pdv' ? 'pontos' : 'pedidos'}-seda-de-favela-${today()}.csv`, rows.map(r => r.map(q).join(';')).join('\n')) }
  if (!can.write()) return;
  if (act === 'newPdv') return pdvForm();
  if (act === 'edit') return pdvForm(id);
  if (act === 'newPed') return pedForm(id);
  if (act === 'editPed') return pedForm(null, id, a.dataset.p);
  if (act === 'tri') { const p = pdvs.get(id), prev = p.status; fire(updateDoc(pref(id), { status: st, atualizado: today(), atualizadoPor: me.email })); toast(`${p.nome}: ${ST[st]}`, () => fire(updateDoc(pref(id), { status: prev }))); return }
  if (act === 'clrFlag') return fire(updateDoc(pref(id), { flags: [] }), 'Observação resolvida');
  if (act === 'pago' || act === 'delPed') { const p = pdvs.get(a.dataset.p), o = (p.hist || []).find(x => x.id === id); if (!o) return;
    if (act === 'pago') return fire(updateDoc(pref(p.id), { hist: p.hist.map(x => x.id === id ? { ...x, pg: 'pago' } : x) }), 'Marcado como pago');
    fire(updateDoc(pref(p.id), { hist: p.hist.filter(x => x.id !== id) })); toast('Registro apagado', () => fire(updateDoc(pref(p.id), { hist: arrayUnion(clone(o)) }), 'Registro restaurado')); return }
  if (!can.admin()) return;
  if (act === 'bonif') return bonForm(id);
  if (act === 'delBon') { const b = bons.find(x => x.id === id); fire(deleteDoc(doc(db, 'bonus', id))); toast('Bonificação removida', () => fire(setDoc(doc(db, 'bonus', id), stripId(b)))); return }
  if (act === 'delPdv') { if (a.dataset.sure !== '1') { a.dataset.sure = '1'; a.textContent = 'Toque de novo para excluir'; return }
    const p = pdvs.get(id); fire(deleteDoc(pref(id))); dlg.close(); toast(`${p.nome} excluído`, () => fire(setDoc(pref(id), stripId(p)), 'Ponto restaurado')); return }
  if (act === 'ativo') { const x = acessos.get(id); return fire(updateDoc(doc(db, 'acessos', id), { ativo: !x.ativo }), x.ativo ? 'Acesso desativado' : 'Acesso reativado') }
  if (act === 'reset') return sendPasswordResetEmail(auth, id).then(() => toast('Link de nova senha enviado para ' + id)).catch(x => toast('Não enviou (' + x.code + ')'));
});
document.addEventListener('change', async e => {
  const t = e.target;
  if (t.matches('select[data-act=papel]') && can.admin()) return fire(updateDoc(doc(db, 'acessos', t.dataset.id), { papel: t.value }), 'Papel alterado');
  if (t.id === 'impF' && t.files[0]) importar(t.files[0]);
});
document.addEventListener('keydown', e => { if (e.key === 'Enter' && e.target.matches('tr[data-act]')) detail(e.target.dataset.id) });
document.addEventListener('input', e => { const m = { fq: 'q', fst: 'st', fcid: 'cid', ftipo: 'tipo', fsort: 'sort' }[e.target.id]; if (m) { F[m] = e.target.value; render() } });
addEventListener('hashchange', () => { if (location.hash === '#novo') { if (me && can.write()) pedForm() } else { render(); scrollTo({ top: 0 }) } });
addEventListener('load', () => { if (location.hash === '#novo') setTimeout(() => { if (me && can.write()) pedForm() }, 1500) });

/* ---------- importação do painel antigo ---------- */
async function importar(file) {
  const msg = { set textContent(t) { impTxt = t; const e = $('#impMsg'); if (e) e.textContent = t } }; if (!navigator.onLine) { msg.textContent = 'A importação precisa de internet.'; return }
  try {
    const j = JSON.parse(await file.text()); if (!Array.isArray(j.pdvs)) throw new Error('arquivo sem pontos');
    const hist = new Map();
    for (const o of j.pedidos || []) { if (!hist.has(o.pdv)) hist.set(o.pdv, []); hist.get(o.pdv).push({ id: o.id || rid(), t: 'p', d: o.data, q: +o.qtd || 0, v: +o.valor || 0, s: has(o.sobra) ? +o.sobra : null, pg: o.pagamento || 'pago', o: o.obs || '', por: '', pn: 'Painel antigo', em: 0 }) }
    const ops = j.pdvs.map(({ id, ...p }) => { const ex = pdvs.get(id), h = [...(ex?.hist || [])]; for (const e of hist.get(id) || []) if (!h.some(x => x.id === e.id)) h.push(e); return [id, { ...p, ...(ex ? stripId(ex) : {}), hist: h }] });
    let n = 0; for (let i = 0; i < ops.length; i += 400) { const b = writeBatch(db); for (const [id, d] of ops.slice(i, i + 400)) b.set(pref(id), d); await b.commit(); n += Math.min(400, ops.length - i); msg.textContent = `Importando… ${n} de ${ops.length}` }
    for (const b of j.bonus || []) await setDoc(doc(db, 'bonus', b.id || rid()), { pdv: b.pdv, desc: b.desc, data: b.data });
    if (j.config) await setDoc(doc(db, 'config', 'geral'), { ...clone(DEF), ...j.config });
    msg.textContent = `Pronto: ${ops.length} pontos e ${(j.pedidos || []).length} pedidos importados.`; toast('Importação concluída');
  } catch (x) { msg.textContent = 'Não importou: ' + (x.code || x.message) }
}
