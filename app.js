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
const DEFV = { a: 1, b: 15, c: 3, d: 1, niveis: [
  { nome: 'Corre', min: 0, premio: 'Reconhecimento no grupo da equipe' },
  { nome: 'Firme', min: 60, premio: 'Bônus de R$ 50' },
  { nome: 'Brabo', min: 150, premio: 'Bônus de R$ 150' },
  { nome: 'Lenda', min: 300, premio: 'Bônus de R$ 300 e destaque no Instagram da marca' }] };
const EMP_PADRAO = { fantasia: 'Seda de Favela', razao: '', doc: '41.048.258/0001-45', ie: '15.157.07-0', endereco: 'Rua Mário Marrocos, 56', bairro: 'Pião', cidade: 'São Gonçalo', uf: 'RJ', cep: '24455-520', tel: '(21) 99777-4435', email: 'sedadefavela@gmail.com', site: 'sedadefavela.com.br', insta: '@sedadefavela', pix: '41048258000145', pixTipo: 'CNPJ', banco: 'PicPay', rodape: '' };
const DEFC = { niveis: [
  { nome: 'Parceiro', med: 0, meses: 0, pont: 0, ben: 'Preço de tabela e visita no ciclo de reposição' },
  { nome: 'Parceiro Fiel', med: 3, meses: 2, pont: 80, ben: '1 piteira de papel de brinde a cada 5 displays no pedido' },
  { nome: 'Ponto Forte', med: 8, meses: 3, pont: 90, ben: 'Preço da faixa de 5 displays em qualquer pedido' },
  { nome: 'Ponto Referência', med: 15, meses: 5, pont: 90, ben: 'Preço da faixa de 15 displays, display de vitrine e destaque no Instagram da marca' }], ind: '1 display de brinde quando o ponto indicado fizer o 2º pedido' };
const DEFM = { novo: 5, travaDias: 15, niveis: [
  { nome: 'Começando', min: 0, premio: 'Sem bônus no mês' },
  { nome: 'Meta batida', min: 60, premio: 'R$ 60' },
  { nome: 'Destaque', min: 120, premio: 'R$ 150' },
  { nome: 'Referência', min: 200, premio: 'R$ 300 e destaque no Instagram da marca' }] };
const DEF = { prazo: 15, unidade: 'caixa', preco: 0, ciclo: 15, ptsCaixa: 10, ptsPontual: 5, ptsIndicacao: 30, janela: 90, niveis: [
  { nome: 'Pista', min: 0, premio: 'Preço de tabela e visita garantida no ciclo' },
  { nome: 'Bonde', min: 100, premio: 'Brinde em cada pedido (piteira, isqueiro ou bag)' },
  { nome: 'Quebrada', min: 250, premio: '1 caixa bônus a cada 10 compradas' },
  { nome: 'Coroa', min: 500, premio: '10% off, display de vitrine e destaque no Instagram da marca' }] };

/* ---------- estado ---------- */
let app, auth, db, me = null, started = false, unsubs = [];
let pdvs = new Map(), evs = [], peds = [], bons = [], cfg = { ...clone(DEF), bv: clone(DEFV), clube: clone(DEFC), meta: clone(DEFM) }, acessos = new Map(), M = new Map();
let impTxt = '', pending = 0, cached = true, F = { q: '', st: '', cid: '', tipo: '', sort: 'nome', ven: '' }, rcid = '', per = 90, skip = new Set(), undo = null, openId = null, installEvt = null, ip = 'mes', iv = 'emp', pq = '', tp = 'mes', colabOpen = null, cargas = [], ilf = 'ativo';
const can = { write: () => me && me.papel !== 'leitura', admin: () => me && me.papel === 'admin', gest: () => me && me.papel !== 'vendedor', dono: () => me && me.papel === 'admin' && !!me.vende };
const papelNome = a => a?.papel === 'admin' && a?.vende ? 'Administrador e vendedor' : PAPEIS[a?.papel] || 'Colaborador';

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

function stopAll() { unsubs.forEach(u => u()); unsubs = []; started = false; me = null; pdvs = new Map(); bons = []; acessos = new Map(); cargas = [] }

function resolveRole(u) {
  const email = (u.email || '').toLowerCase();
  const isRoot = email === ADMIN_EMAIL.toLowerCase();
  gate('Conferindo seu acesso…');
  unsubs.push(onSnapshot(doc(db, 'acessos', email), s => {
    const a = s.exists() ? s.data() : null;
    if (isRoot) me = { email, nome: a?.nome || 'Administradora', papel: 'admin', vende: !!a?.vende };
    else if (!a) { me = null; return gate(`O e-mail ${email} ainda não tem acesso. Peça para a administradora liberar.`, { out: true }) }
    else if (!a.ativo) { me = null; return gate('Seu acesso está desativado. Fale com a administradora.', { out: true }) }
    else me = { email, nome: a.nome || email, papel: a.papel || 'vendedor', vende: !!a.vende };
    document.body.classList.toggle('ro', !can.write()); document.body.classList.toggle('notadm', !can.admin()); document.body.classList.toggle('vend', !can.gest());
    $('#whoName').textContent = me.nome === papelNome(me) ? me.nome : `${me.nome} · ${papelNome(me)}`;
    document.querySelectorAll('[data-admin]').forEach(a => a.hidden = !can.admin()); document.body.classList.toggle('adm', can.admin());
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
  unsubs.push(onSnapshot(doc(db, 'config', 'cargas'), s => { cargas = s.exists() && Array.isArray(s.data().mov) ? s.data().mov : []; render() }, fail));
  unsubs.push(onSnapshot(collection(db, 'bonus'), s => { bons = s.docs.map(d => ({ ...d.data(), id: d.id })); render() }, fail));
  unsubs.push(onSnapshot(doc(db, 'config', 'geral'), s => { cfg = s.exists() ? { ...clone(DEF), ...s.data() } : clone(DEF); if (!Array.isArray(cfg.niveis) || cfg.niveis.length !== 4) cfg.niveis = clone(DEF.niveis); cfg.bv = { ...clone(DEFV), ...(cfg.bv || {}) }; if (!Array.isArray(cfg.bv.niveis) || cfg.bv.niveis.length !== 4) cfg.bv.niveis = clone(DEFV.niveis); cfg.clube = { ...clone(DEFC), ...(cfg.clube || {}) }; if (!Array.isArray(cfg.clube.niveis) || cfg.clube.niveis.length !== 4) cfg.clube.niveis = clone(DEFC.niveis); cfg.meta = { ...clone(DEFM), ...(cfg.meta || {}) }; if (!Array.isArray(cfg.meta.niveis) || cfg.meta.niveis.length !== 4) cfg.meta.niveis = clone(DEFM.niveis); render() }, fail));
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
function clubeNivel(s) { let n = 0; cfg.clube.niveis.forEach((t, i) => { if (i && s.med >= +t.med && s.meses >= +t.meses && (s.pont === null || s.pont >= +t.pont)) n = i }); return s.n ? n : 0 }
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
    s.ind = indic.get(p.id) || 0;
    { const q90 = ps.filter(o => t - D(o.d) < 90).reduce((a, o) => a + (+o.q || 0), 0), m6 = new Set(ps.filter(o => t - D(o.d) < 183).map(o => o.d.slice(0, 7)));
      const prz = ps.filter(o => t - D(o.d) < 183 && o.venc && (o.pg === 'pago' || D(o.venc) < t)), ok = prz.filter(o => o.pg === 'pago' && (!o.pgEm || D(o.pgEm) <= D(o.venc) + 3)).length;
      s.med = q90 / 3; s.meses = m6.size; s.pont = prz.length ? Math.round(ok / prz.length * 100) : null; s.nivel = clubeNivel(s) }
    M.set(p.id, s);
  }
}
const FP = ['PIX', 'Dinheiro', 'Cartão', 'Boleto', 'A prazo'];
const brD = s => s ? s.slice(8, 10) + '/' + s.slice(5, 7) + '/' + s.slice(0, 4) : '';
const emp = () => { const e = { ...EMP_PADRAO }; for (const [k, v] of Object.entries(cfg.empresa || {})) if (has(v) && String(v).trim()) e[k] = v; return e };
function produtos() { const l = Array.isArray(cfg.produtos) && cfg.produtos.length ? cfg.produtos : [{ c: 'SDF-CX', d: 'Seda de Favela (caixa)', cat: 'Sedas', un: 'CX', p: +cfg.preco || 0, ncm: '4813.10.00', f: 1 }]; return l }
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
const tier = i => `<span class="tier ${i === 3 ? 't3' : ''}">${esc(cfg.clube.niveis[i]?.nome)}</span>`;
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
  $('#sub').textContent = can.gest() ? `${all.length} pontos · ${peds.length} pedidos registrados` : `${meusP().length} pontos seus · ${peds.filter(o => o.por === me.email).length} pedidos seus`;
  const tb = $('#tabs a[data-cob]'); if (tb) { const n = receber().filter(o => diasPara(o) !== null && diasPara(o) <= 1).length; tb.querySelector('b')?.remove(); if (n) tb.insertAdjacentHTML('beforeend', ` <b>${n}</b>`) }
}

/* ---------- telas ---------- */
function rcard(p) { const s = M.get(p.id), late = s.dAte < 0;
  return `<div class="card ${late ? 'late' : ''}"><div class="ct"><div><button class="nm" data-act="open" data-id="${esc(p.id)}">${esc(p.nome)}</button><div class="pl">${esc(lugar(p))}</div></div>
  <div class="due"><span class="num">${fd(s.prox)}</span><small>${late ? 'atrasado ' : ''}${rel(s.dAte)}</small></div></div>
  <div class="meta"><span>Último pedido <b>${fd(s.last.d)}</b> · ${nf(s.last.q)} ${esc(Us(+s.last.q))}</span>${s.lastEv && s.lastEv.t === 'v' ? `<span>Visita <b>${fd(s.lastEv.d)}</b></span>` : ''}${s.giro ? `<span>Giro <b>${nf(s.giro)}/sem</b>${s.medido ? '' : ' (estimado)'}</span>` : ''}<span>${tier(s.nivel)}</span></div>
  <div class="cb"><button class="btn sm ink" data-w data-act="newPed" data-id="${esc(p.id)}">Registrar</button>${wa(p)}${mapa(p)}</div></div>` }

function vRepor() {
  const base = can.gest() ? [...pdvs.values()] : meusP(), at = base.filter(p => p.status === 'ativo');
  const cids = [...new Set(at.filter(p => M.get(p.id).last).map(p => p.cidade).filter(Boolean))].sort();
  const wl = at.filter(p => M.get(p.id).last && (!rcid || p.cidade === rcid)).sort((a, b) => M.get(a.id).dAte - M.get(b.id).dAte);
  const g = [['Atrasados', wl.filter(p => M.get(p.id).dAte < 0)], ['Hoje até 3 dias', wl.filter(p => { const d = M.get(p.id).dAte; return d >= 0 && d <= 3 })], ['Esta semana', wl.filter(p => { const d = M.get(p.id).dAte; return d > 3 && d <= 7 })], ['Mais pra frente', wl.filter(p => M.get(p.id).dAte > 7)]];
  const semPed = at.filter(p => !M.get(p.id).last && (!rcid || p.cidade === rcid)), pro = base.filter(p => p.status === 'prospeccao' && (!rcid || p.cidade === rcid)).sort((a, b) => (a.proxContato || '9') < (b.proxContato || '9') ? -1 : 1);
  const ver = [...pdvs.values()].filter(p => p.status === 'verificar').length;
  let h = `<h2>Quem repor</h2><p class="lead">A data vem do ritmo de cada ponto. Anote a sobra que encontrar em cada visita, mesmo sem pedido: é ela que mostra quanto o ponto vende por semana.</p>`;
  if (cids.length > 1) h += `<div class="chips"><button class="chip ${!rcid ? 'on' : ''}" data-act="rcid" data-v="">Todas</button>${cids.map(c => `<button class="chip ${rcid === c ? 'on' : ''}" data-act="rcid" data-v="${esc(c)}">${esc(c)}</button>`).join('')}</div>`;
  if (!can.gest() && !base.length) h += `<div class="empty">Nenhum ponto no seu nome ainda. Os pontos que você cadastrar ou atender aparecem aqui.</div>`;
  if (!peds.length && can.gest()) h += `<div class="hero"><div><h3 style="margin-top:0">Comece por aqui</h3><ol class="steps">
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
  const all = can.gest() ? [...pdvs.values()] : meusP(), cids = [...new Set(all.map(p => p.cidade).filter(Boolean))].sort(), q = F.q.trim().toLowerCase();
  let l = all.filter(p => (!F.st || p.status === F.st) && (!F.cid || p.cidade === F.cid) && (!F.tipo || p.tipo === F.tipo) && (!F.ven || (F.ven === '-' ? !conquistador(p) : conquistador(p) === F.ven)) && (!q || [p.nome, p.bairro, p.cidade, p.endereco, p.contato].join(' ').toLowerCase().includes(q)));
  const S = { nome: (a, b) => a.nome.localeCompare(b.nome), prox: (a, b) => (M.get(a.id).dAte ?? 1e9) - (M.get(b.id).dAte ?? 1e9), compra: (a, b) => qtdEm(b.id, 90) - qtdEm(a.id, 90), ult: (a, b) => (M.get(b.id).last?.d || '') > (M.get(a.id).last?.d || '') ? 1 : -1 };
  l.sort(S[F.sort]);
  const opt = (v, t, c) => `<option value="${esc(v)}" ${c === v ? 'selected' : ''}>${esc(t)}</option>`;
  return `<h2>${can.gest() ? 'Todos os pontos' : 'Meus pontos'}</h2><p class="lead">${l.length} de ${all.length} pontos${can.gest() ? '' : ' no seu nome ou que você atende'}.</p>
  <div class="bar"><input id="fq" type="search" placeholder="Buscar nome, bairro, telefone…" value="${esc(F.q)}" aria-label="Buscar">
  <select id="fst" aria-label="Status">${opt('', 'Todos os status', F.st)}${Object.entries(ST).map(([k, v]) => opt(k, v, F.st)).join('')}</select>
  <select id="fcid" aria-label="Cidade">${opt('', 'Todas as cidades', F.cid)}${cids.map(c => opt(c, c, F.cid)).join('')}</select>
  <select id="ftipo" aria-label="Tipo">${opt('', 'Todos os tipos', F.tipo)}${TIPOS.map(t => opt(t, t, F.tipo)).join('')}</select>
  ${can.gest() ? `<select id="fven" aria-label="Conquistado por">${opt('', 'Todos os vendedores', F.ven)}${opt('-', 'Sem vendedor definido', F.ven)}${colabs().map(e => opt(e, nomeDe(e), F.ven)).join('')}</select>` : ''}
  <select id="fsort" aria-label="Ordenar">${opt('nome', 'A a Z', F.sort)}${opt('prox', 'Próxima reposição', F.sort)}${opt('compra', 'Mais compram (90 dias)', F.sort)}${opt('ult', 'Pedido mais recente', F.sort)}</select>
  <button class="btn line" data-w data-act="newPdv">+ Ponto</button></div>
  ${can.admin() && l.length && l.length < all.length ? `<div class="lote card"><span>Definir <b>Conquistado por</b> para os <b>${l.length}</b> pontos desta lista:</span><select id="loteV"><option value="">Escolha o vendedor</option>${colabs().map(e => `<option value="${esc(e)}">${esc(nomeDe(e))}</option>`).join('')}<option value="-">Ninguém (tirar vendedor)</option></select><button class="btn sm ink" data-act="lote" data-ids='${esc(JSON.stringify(l.map(p => p.id)))}'>Aplicar</button></div>` : ''}
  ${l.length ? `<table class="stack"><thead><tr><th>Ponto</th><th>Status</th>${can.gest() ? '<th>Conquistado por</th>' : ''}<th>Tipo</th><th>Último pedido</th><th>Repor</th><th class="r">${esc(U())}s 90d</th><th>Nível</th></tr></thead><tbody>
  ${l.map(p => { const s = M.get(p.id); return `<tr tabindex="0" data-act="open" data-id="${esc(p.id)}"><td><b>${esc(p.nome)}</b><div class="pl">${esc(lugar(p))}</div></td><td>${pill(p.status)}${p.flags?.length ? ' <span class="pill">!</span>' : ''}</td>${can.gest() ? `<td>${conquistador(p) ? esc(nomeDe(conquistador(p))) : '<span class="pl">não definido</span>'}</td>` : ''}<td>${esc(p.tipo)}</td><td>${s.last ? fd(s.last.d) : ''}</td><td>${s.prox && p.status === 'ativo' ? `${fd(s.prox)} <span class="pl">${rel(s.dAte)}</span>` : ''}</td><td class="r">${s.n ? nf(qtdEm(p.id, 90)) : ''}</td><td>${s.n ? tier(s.nivel) : ''}</td></tr>` }).join('')}</tbody></table>` : `<div class="empty">Nenhum ponto com esses filtros.</div>`}` }

function lista(t, rows, fmt) { const mx = Math.max(1, ...rows.map(r => r.v));
  return `<div class="rk"><h3>${t} <span>${rows.length}</span></h3>${rows.length ? '<div class="scrollbox">' + rows.map((r, i) => `<div class="rr" ${r.id ? `data-act="open" data-id="${esc(r.id)}"` : ''}><i>${i + 1}</i><span class="n">${esc(r.n)}</span><span class="v">${fmt(r.v)}</span><div class="tr"><div style="width:${(r.v / mx * 100).toFixed(1)}%"></div></div></div>`).join('') + '</div>' : '<p class="pl">Sem pedidos nesse período.</p>'}</div>` }
function vRanking() {
  const t = D(today()), ps = peds.filter(o => per === 0 || t - D(o.d) < per), agg = new Map(), ven = new Map(), cid = new Map();
  for (const o of ps) { const a = agg.get(o.pdv) || { q: 0, n: 0 }; a.q += +o.q || 0; a.n++; agg.set(o.pdv, a); const v = o.pn || o.por || 'Painel antigo'; ven.set(v, (ven.get(v) || 0) + (+o.q || 0)); const c = pdvs.get(o.pdv)?.cidade || 'Sem cidade'; cid.set(c, (cid.get(c) || 0) + (+o.q || 0)) }
  const nm = id => pdvs.get(id)?.nome || 'Ponto removido', top = a => a.sort((x, y) => y.v - x.v);
  const P = [[30, '30 dias'], [90, '90 dias'], [365, '12 meses'], [0, 'Tudo']];
  return `<h2>Ranking</h2><p class="lead">"Mais vendem" é o giro: quanto sai do ponto por semana, medido pela sobra anotada nas visitas.</p>
  <div class="chips">${P.map(([v, l]) => `<button class="chip ${per === v ? 'on' : ''}" data-act="per" data-v="${v}">${l}</button>`).join('')}</div>
  <div class="cols">${lista(`Mais compram (${esc(U())}s)`, top([...agg].map(([id, a]) => ({ id, n: nm(id), v: a.q }))), nf)}
  ${lista(`Mais vendem (${esc(U())}s/semana)`, top([...pdvs.values()].map(p => ({ id: p.id, n: p.nome, v: M.get(p.id).giro })).filter(r => r.v > 0)), nf)}
  ${lista('Mais pedidos feitos', top([...agg].map(([id, a]) => ({ id, n: nm(id), v: a.n }))), v => v)}
  ${lista(`Por vendedor (${esc(U())}s)`, top([...ven].map(([n, v]) => ({ n, v }))), nf)}
  ${lista(`Por cidade (${esc(U())}s)`, top([...cid].map(([n, v]) => ({ n, v }))), nf)}</div>` }

function vBonus() {
  const C = cfg.clube, at = [...pdvs.values()].filter(p => p.status === 'ativo' && M.get(p.id).n).sort((a, b) => M.get(b.id).nivel - M.get(a.id).nivel || M.get(b.id).med - M.get(a.id).med);
  const cnt = C.niveis.map((_, i) => at.filter(p => M.get(p.id).nivel === i).length);
  const falta = (s) => { const nx = C.niveis[s.nivel + 1]; if (!nx) return 'Nível máximo'; const f = [];
    if (s.med < +nx.med) f.push(`média de ${nf(+nx.med)}/mês (hoje ${nf(s.med)})`); if (s.meses < +nx.meses) f.push(`comprar em ${+nx.meses} dos últimos 6 meses (hoje ${s.meses})`); if (s.pont !== null && s.pont < +nx.pont) f.push(`${+nx.pont}% pago em dia (hoje ${s.pont}%)`);
    return `Pra ${esc(nx.nome)}: ${f.join(', ')}` };
  return `<h2>Clube de parceiros</h2><p class="lead">Bonificação dos <b>clientes</b> (pontos de venda). O bônus dos vendedores fica em Equipe. O nível vem do que o ponto faz de verdade: quanto compra por mês (média dos últimos 90 dias), se compra todo mês (últimos 6 meses) e se paga no prazo. Sobe devagar e cai se o ponto parar ou atrasar. Indicação: ${esc(C.ind)}.</p>
  <div class="tiers">${C.niveis.map((t, i) => `<div class="tc ${i === 3 ? 'top3' : ''}"><span class="num">${esc(t.nome)}</span><span class="q">${i ? `${nf(+t.med)} ${esc(U())}s/mês · compra em ${+t.meses} de 6 meses · ${+t.pont}% em dia` : 'todo ponto ativo com pedido'} · ${cnt[i]} ${cnt[i] === 1 ? 'ponto' : 'pontos'}</span><span>${esc(t.ben)}</span></div>`).join('')}</div>
  <h3>Pontos no clube <span>${at.length}</span></h3>
  ${at.length ? `<div class="scrollbox tall"><table class="stack"><thead><tr><th>Ponto</th><th>Nível</th><th class="r">Média/mês</th><th class="r">Meses comprando</th><th class="r">Pago em dia</th><th>Próximo passo</th><th></th></tr></thead><tbody>${at.map(p => { const s = M.get(p.id);
   return `<tr data-act="open" data-id="${esc(p.id)}" tabindex="0"><td><b>${esc(p.nome)}</b><div class="pl">${esc(lugar(p))}</div></td><td>${tier(s.nivel)}</td><td class="r">${nf(s.med)}</td><td class="r">${s.meses} de 6</td><td class="r">${s.pont === null ? '<span class="pl">só à vista</span>' : s.pont + '%'}</td><td class="pl">${falta(s)}</td><td><button class="btn sm line" data-adm data-act="bonif" data-id="${esc(p.id)}">Bonificar</button></td></tr>` }).join('')}</tbody></table></div>` : `<div class="empty">Os pontos entram aqui quando estão ativos e têm pedido registrado.</div>`}
  <h3>Bonificações entregues <span>${bons.length}</span></h3>
  ${bons.length ? `<ul class="hist">${[...bons].sort((a, b) => a.data < b.data ? 1 : -1).slice(0, 40).map(b => `<li><span><b>${esc(pdvs.get(b.pdv)?.nome || 'Ponto removido')}</b> · ${fd(b.data)}<br><span class="pl">${esc(b.desc)}</span></span><button class="lk" data-adm data-act="delBon" data-id="${esc(b.id)}">Remover</button></li>`).join('')}</ul>` : `<div class="empty">Quando entregar um benefício, toque em Bonificar para ficar registrado.</div>`}` }

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
  return `<h2>Acessos</h2><p class="lead">Cada pessoa entra com o próprio e-mail e senha. <b>Administrador e vendedor</b> (dono) vê o painel da empresa e também os próprios números de venda. <b>Vendedor</b> cadastra pontos, registra pedidos e visitas e faz triagem. <b>Só leitura</b> vê tudo e não altera nada. Desativar corta o acesso na hora, sem apagar o que a pessoa registrou.</p>
  <form id="teamF" class="f card" style="padding:18px;margin-bottom:18px">
   <label>Nome<input name="nome" required autocomplete="off"></label>
   <label>E-mail<input name="email" type="email" required autocomplete="off"></label>
   <label>Papel<select name="papel"><option value="vendedor">Vendedor</option><option value="leitura">Só leitura</option><option value="admin">Administradora</option><option value="adminv">Administrador e vendedor (dono)</option></select></label>
   <label>Senha inicial<input name="senha" minlength="6" required autocomplete="new-password"><small>Mínimo 6 caracteres. Passe para a pessoa e peça para trocar em "Esqueci minha senha".</small></label>
   <div class="fa w"><button class="btn ink">Dar acesso</button></div></form>
  ${l.length ? `<table class="stack"><thead><tr><th>Pessoa</th><th>Papel</th><th>Status</th><th class="r">Registros</th><th></th></tr></thead><tbody>${l.map(([em, a]) => `<tr><td><b>${esc(a.nome)}</b><div class="pl">${esc(em)}</div></td>
   <td><select data-act="papel" data-id="${esc(em)}" aria-label="Papel" ${em === me.email ? 'disabled' : ''}>${[...Object.entries(PAPEIS), ['adminv', 'Administrador e vendedor']].map(([k, v]) => `<option value="${k}" ${(a.papel === 'admin' && a.vende ? 'adminv' : a.papel) === k ? 'selected' : ''}>${v}</option>`).join('')}</select></td>
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
  ${ad ? `<h3 id="empresa">Dados da empresa e PIX <span>saem no comprovante e no lembrete de pagamento</span></h3>
  <form id="empF" class="f card" style="padding:20px">${[['fantasia', 'Nome no comprovante'], ['pix', 'Chave PIX'], ['pixTipo', 'Tipo da chave (CNPJ, e-mail, celular, aleatória)'], ['banco', 'Banco da chave'], ['razao', 'Razão social (opcional)', 'w'], ['doc', 'CNPJ'], ['ie', 'Inscrição estadual'], ['endereco', 'Endereço com número', 'w'], ['bairro', 'Bairro'], ['cidade', 'Cidade'], ['uf', 'UF'], ['cep', 'CEP'], ['tel', 'Telefone / WhatsApp'], ['email', 'E-mail'], ['insta', 'Instagram'], ['site', 'Site'], ['rodape', 'Texto do rodapé do comprovante', 'w']].map(([k, l, w]) => `<label class="${w || ''}">${l}<input name="${k}" value="${esc(emp()[k])}"></label>`).join('')}
  <label class="w" style="flex-direction:row;gap:10px;align-items:center"><input type="checkbox" name="controlaNF" ${cfg.controlaNF === false ? '' : 'checked'} style="width:22px;min-height:22px"> Controlar emissão de NF-e em cada pedido</label>
  <div class="fa w"><button class="btn ink">Salvar dados da empresa</button></div></form>` : ''}
  <h3>Regras</h3>
  <form id="cfgF" class="f card" style="padding:20px"><fieldset ${ad ? '' : 'disabled'} style="display:contents">
  <label>Unidade de venda<input name="unidade" value="${esc(cfg.unidade)}" required></label>
  <label>Preço por ${esc(U())} (R$)<input name="preco" type="number" step="0.01" min="0" value="${+cfg.preco}"></label>
  <label>Ciclo padrão de reposição (dias)<input name="ciclo" type="number" min="1" value="${+cfg.ciclo}"></label>
  <label>Prazo padrão de pagamento (dias)<input name="prazo" type="number" min="0" value="${+cfg.prazo || 15}"><small>Venda a prazo já sai com vencimento daqui a esses dias</small></label><span></span>
  <h3 class="w" style="margin:18px 0 0">Clube de parceiros (clientes)</h3><p class="pl w" style="margin:0">Nível do ponto pela média de compra por mês (últimos 90 dias), meses comprando (últimos 6) e % pago em dia.</p>
  ${cfg.clube.niveis.map((t, i) => `<label>Nível ${i + 1}<input name="cn${i}" value="${esc(t.nome)}" required></label>${i ? `<label>Média mínima/mês<input name="cm${i}" type="number" min="0" step="0.5" value="${+t.med}"></label><label>Meses comprando (de 6)<input name="cs${i}" type="number" min="0" max="6" value="${+t.meses}"></label><label>% pago em dia<input name="cp${i}" type="number" min="0" max="100" value="${+t.pont}"></label>` : '<span></span>'}<label class="w">Benefício<input name="cb${i}" value="${esc(t.ben)}"></label>`).join('')}
  <label class="w">Indicação<input name="cind" value="${esc(cfg.clube.ind)}"></label>
  <h3 class="w" style="margin:18px 0 0">Meta da equipe (mensal)</h3><p class="pl w" style="margin:0">Conta ${esc(U())}s vendidas e já pagas no mês (pela data do pagamento). Venda a receber entra quando for paga.</p>
  <label>Ponto novo que recomprou vale (${esc(U())}s)<input name="mnovo" type="number" min="0" value="${+cfg.meta.novo}"></label>
  <label>Bônus fica retido se tiver cobrança vencida há mais de (dias)<input name="mtrava" type="number" min="0" value="${+cfg.meta.travaDias}"></label>
  ${cfg.meta.niveis.map((t, i) => `<label>Nível ${i + 1}<input name="vn${i}" value="${esc(t.nome)}" required></label><label>A partir de (${esc(U())}s no mês)<input name="vm${i}" type="number" min="0" value="${+t.min}" ${i ? '' : 'readonly'}></label><label class="w">Prêmio<input name="vp${i}" value="${esc(t.premio)}"></label>`).join('')}
  ${ad ? '<div class="fa w"><button class="btn ink">Salvar ajustes</button></div>' : ''}</fieldset></form>
  ${ad ? `
  <h3>Produtos</h3><p class="lead">${produtos().length} produtos cadastrados. <a class="lk" href="#produtos">Abrir a lista de produtos</a></p>` : ''}
  <h3>Exportar</h3><div class="cb"><button class="btn ink" data-act="xlsx">Planilha completa (Excel)</button><button class="btn line" data-act="csv" data-v="pdv">Baixar pontos (.csv)</button><button class="btn line" data-act="csv" data-v="ped">Baixar pedidos e visitas (.csv)</button></div>
  ${ad ? `<h3>Importar do painel antigo</h3><p class="lead">Use uma vez, com internet, com o arquivo pdvs-importacao.json. Pontos que já existem recebem só o histórico que faltar; nada é apagado.</p><label class="btn line" style="width:fit-content">Escolher arquivo<input type="file" id="impF" accept=".json,application/json" hidden></label><p class="pl" id="impMsg">${esc(impTxt)}</p>` : ''}` }

function vMais() {
  const ios = /iphone|ipad|ipod/i.test(navigator.userAgent), standalone = matchMedia('(display-mode: standalone)').matches || navigator.standalone;
  return `<h2>Mais</h2><div class="menu">
  ${can.gest() ? `<a href="#repor">Reposição <span>quem está perto de repor</span></a><a href="#produtos">Produtos <span>${produtos().length} cadastrados</span></a><a href="#bonus">Clube de parceiros <span>bonificação dos clientes (pontos de venda)</span></a><a href="#ranking">Ranking <span>quem mais compra e mais vende</span></a><a href="#triagem">Triagem <span>${[...pdvs.values()].filter(p => p.status === 'verificar').length} a verificar</span></a>
  ${can.admin() ? `<a href="#notas">Notas fiscais <span>${peds.filter(o => o.nf && o.nf.st !== 'emitida').length} a emitir</span></a><a href="#equipe">Acessos <span>quem entra no app e com qual papel</span></a>` : ''}
  <a href="#ajustes">Ajustes e exportar <span>dados da empresa, PIX, regras e planilhas</span></a>` : `<a href="#pontos">Meus pontos <span>${meusP().length} no seu nome ou que você atende</span></a><a href="#cobrar">Cobranças <span>lembretes de pagamento</span></a>`}
  ${!standalone && installEvt ? '<button data-act="install">Instalar app no celular <span>Android</span></button>' : ''}
  <button data-act="logout">Sair <span>${esc(me?.email || '')}</span></button></div>
  ${!standalone && ios ? `<div class="card" style="margin-top:16px;max-width:520px"><b>Instalar no iPhone</b><ol class="steps"><li>Abra este endereço no <b>Safari</b>.</li><li>Toque em <b>Compartilhar</b> (quadrado com seta pra cima).</li><li>Escolha <b>Adicionar à Tela de Início</b> e confirme.</li></ol></div>` : ''}
  <p class="pl" style="margin-top:18px">PDVs Seda de Favela · ${esc(PAPEIS[me?.papel] || '')}${navigator.onLine ? '' : ' · sem internet'}</p>` }

/* ---------- início: capa com os números de cada vendedor ---------- */
const nomeDe = email => { if (!email) return 'Sem vendedor'; const a = acessos.get(email); if (a?.nome) return a.nome; if (me && email === me.email) return me.nome;
  const o = peds.find(x => x.por === email && x.pn); if (o) return o.pn; for (const p of pdvs.values()) if (p.criadoPor === email && p.criadoPorNome) return p.criadoPorNome; return email.split('@')[0] };
function conquistador(p) { if (p.dono) return p.dono; if (p.criadoPor) return p.criadoPor; const f = M.get(p.id)?.ps.find(o => o.por); return f ? f.por : '' }
const meusP = () => [...pdvs.values()].filter(p => p.status !== 'fechou' && (conquistador(p) === me.email || (p.hist || []).some(e => e.por === me.email)));
const conqD = p => (p.criadoPor && p.criado) || M.get(p.id)?.ps[0]?.d || p.criado || '';
function desdeDe(k) { const t = today(); return k === 'mes' ? t.slice(0, 8) + '01' : k === 'd90' ? addD(t, -89) : '0000-00-00' }
function numeros(email, k) { const de = desdeDe(k), mine = o => !email || o.por === email;
  const ps = peds.filter(o => mine(o) && o.d >= de), con = [...pdvs.values()].filter(p => p.status !== 'fechou' && (email ? conquistador(p) === email : conquistador(p)));
  const conP = con.filter(p => conqD(p) >= de);
  return { q: ps.reduce((a, o) => a + (+o.q || 0), 0), n: ps.length, v: ps.reduce((a, o) => a + (+o.v || 0), 0), pts: new Set(ps.map(o => o.pdv)).size,
    con, conP, at: con.filter(p => p.status === 'ativo').length, pro: con.filter(p => p.status === 'prospeccao').length } }
/* ---------- cobranças: prazo, lembrete no WhatsApp com PIX e CNPJ ---------- */
const receber = () => peds.filter(o => o.pg === 'receber' && (can.gest() || o.por === me.email));
const diasPara = o => o.venc ? D(o.venc) - D(today()) : null;
function lembreteTexto(o) { const p = pdvs.get(o.pdv), e = emp(), d = diasPara(o), its = itensDe(o);
  const quando = d === null ? 'está em aberto' : d > 1 ? `vence em ${brD(o.venc)}` : d === 1 ? `vence amanhã (${brD(o.venc)})` : d === 0 ? `vence hoje (${brD(o.venc)})` : `venceu em ${brD(o.venc)}`;
  const pr = (p?.contato && p?.resp) ? p.resp : (p?.nome || '');
  const blocos = [`Oi${pr ? ', ' + pr : ''}! Aqui é da *${e.fantasia}*.`,
    `Passando pra lembrar que o pagamento do pedido *${o.n || o.id}*, deixado aí em ${brD(o.d)}, ${quando}.` + (its.length ? '\n' + its.map(i => `• ${nf(i.q)} ${i.un || ''} ${i.d}`).join('\n') : '') + `\n*Valor: ${brl(o.v)}*`,
    e.pix ? `*Pague por PIX*\nChave PIX (${e.pixTipo || 'chave'}): ${e.pix}${e.banco ? '\nBanco: ' + e.banco : ''}\nFavorecido: ${e.fantasia}${e.razao ? ' (' + e.razao + ')' : ''}\nCNPJ: ${e.doc}` : `Favorecido: ${e.fantasia} · CNPJ: ${e.doc}`,
    `Assim que pagar, manda o comprovante por aqui. Obrigado pela parceria!\n${e.fantasia} · ${e.tel}`];
  return blocos.join('\n\n') }
function waLink(p, msg) { const d = String(p?.contato || '').replace(/\D/g, ''); if (d.length < 10) return ''; return `https://wa.me/${d.length <= 11 ? '55' + d : d}?text=${encodeURIComponent(msg)}` }
function cobItem(o, comVend) { const p = pdvs.get(o.pdv), d = diasPara(o), late = d !== null && d < 0, w = waLink(p, '');
  const tag = d === null ? '' : d < 0 ? `<span class="pill p-verificar">${-d === 1 ? 'venceu ontem' : `venceu há ${-d} dias`}</span>` : d === 0 ? '<span class="pill pend">vence hoje</span>' : d === 1 ? '<span class="pill p-prospeccao">vence amanhã</span>' : `<span class="pill">vence ${fd(o.venc)}</span>`;
  return `<div class="cob ${late ? 'late' : ''}"><div class="cob-t"><div><button class="nm" data-act="open" data-id="${esc(o.pdv)}">${esc(p?.nome || 'Ponto removido')}</button><div class="pl">Pedido ${esc(o.n || '')} · deixado em ${brD(o.d)}${comVend ? ' · ' + esc(o.pn || nomeDe(o.por)) : ''}</div></div><div class="due"><span class="num">${brl(o.v)}</span>${tag}</div></div>
   <div class="cb">${w ? `<button class="btn sm sun" data-act="lemb" data-p="${esc(o.pdv)}" data-id="${esc(o.id)}">Lembrete no WhatsApp</button>` : `<span class="pl">Sem WhatsApp no cadastro do ponto</span>`}<button class="btn sm line" data-w data-act="pago" data-p="${esc(o.pdv)}" data-id="${esc(o.id)}">Recebi</button><button class="btn sm line" data-act="rec" data-p="${esc(o.pdv)}" data-id="${esc(o.id)}">Comprovante</button></div>
   ${o.lemb ? `<div class="pl">Lembrete enviado em ${fd(o.lemb)}</div>` : ''}</div>` }
function vCobrar() { const l = receber().sort((a, b) => (a.venc || '9') < (b.venc || '9') ? -1 : 1), e = emp(), g = can.gest();
  const G = [['Atrasados', l.filter(o => diasPara(o) !== null && diasPara(o) < 0)], ['Vence hoje', l.filter(o => diasPara(o) === 0)], ['Vence amanhã', l.filter(o => diasPara(o) === 1)], ['Próximos 7 dias', l.filter(o => diasPara(o) > 1 && diasPara(o) <= 7)], ['Depois', l.filter(o => diasPara(o) === null || diasPara(o) > 7)]];
  const tot = l.reduce((a, o) => a + (+o.v || 0), 0), atr = G[0][1].reduce((a, o) => a + (+o.v || 0), 0);
  return `<h2>Cobranças</h2><p class="lead">Mercadoria deixada a prazo. Na véspera e no dia do vencimento, toque em <b>Lembrete no WhatsApp</b>: a mensagem já sai pronta com valor, PIX e CNPJ. Quando o ponto pagar, toque em <b>Recebi</b>.</p>
  ${!e.pix ? `<div class="flag" style="margin-bottom:14px">Falta a chave PIX da empresa. ${can.admin() ? '<a class="lk" href="#ajustes">Cadastrar em Ajustes (primeiro quadro)</a>' : 'Peça para a administradora cadastrar.'} Sem ela, o lembrete sai só com o CNPJ.</div>` : ''}
  <div class="mets m3"><div class="met"><span class="num">${brl(tot)}</span><small>a receber${g ? '' : ' dos seus pedidos'}</small></div><div class="met"><span class="num" style="color:${atr ? 'var(--brick)' : 'inherit'}">${brl(atr)}</span><small>atrasado</small></div><div class="met"><span class="num">${G[1][1].length + G[2][1].length}</span><small>lembretes pra mandar hoje</small></div></div>
  ${l.length ? G.filter(([, x]) => x.length).map(([t, x]) => `<h3>${t} <span>${x.length} · ${brl(x.reduce((a, o) => a + (+o.v || 0), 0))}</span></h3><div class="grid">${x.map(o => cobItem(o, g)).join('')}</div>`).join('') : '<div class="empty">Nada a receber. Tudo em dia.</div>'}` }

/* ---------- ranking e movimento da equipe (todos veem; sem mostrar os pontos dos outros) ---------- */
const quando = o => { if (o.em) { const m = Math.round((Date.now() - o.em) / 6e4); if (m < 60) return m <= 1 ? 'agora' : `há ${m} min`; if (m < 24 * 60) return `há ${Math.round(m / 60)} h` } const d = D(today()) - D(o.d); return d === 0 ? 'hoje' : d === 1 ? 'ontem' : `há ${d} dias` };
function rankEquipe() { const ym = ymDe('mes'), r = new Map(), add = (e, k, n) => { if (!e) return; const x = r.get(e) || { q: 0, n: 0, c: 0 }; x[k] += n; r.set(e, x) };
  peds.filter(o => o.d.startsWith(ym) && o.por).forEach(o => { add(o.por, 'q', +o.q || 0); add(o.por, 'n', 1) });
  [...pdvs.values()].forEach(p => { const c = conquistador(p); if (c && p.status !== 'fechou' && conqD(p).startsWith(ym)) add(c, 'c', 1) });
  const l = [...r].sort((a, b) => b[1].q - a[1].q || b[1].c - a[1].c), mx = Math.max(1, ...l.map(x => x[1].q)), pos = l.findIndex(x => x[0] === me.email);
  const ev = [...peds.filter(o => o.por).map(o => ({ e: o.por, nm: o.pn, d: o.d, em: o.em, t: `vendeu ${nf(o.q)} ${Us(+o.q)}` })),
    ...[...pdvs.values()].filter(p => p.criadoPor && p.criado).map(p => ({ e: p.criadoPor, nm: p.criadoPorNome, d: p.criado, em: 0, t: p.status === 'prospeccao' ? 'cadastrou um ponto em prospecção' : 'conquistou um ponto novo' }))]
    .sort((a, b) => a.d < b.d ? 1 : a.d > b.d ? -1 : (b.em || 0) - (a.em || 0)).slice(0, 20);
  const medal = i => i === 0 ? '1º' : i === 1 ? '2º' : i === 2 ? '3º' : (i + 1) + 'º';
  return `<div class="cols" style="margin-top:12px">
   <div class="rk"><h3>Ranking da equipe <span>${esc(nomeMes(ym))}</span></h3>${pos >= 0 ? `<p class="pl" style="margin:-4px 0 8px">Você está em <b>${pos + 1}º</b> de ${l.length}.${pos > 0 ? ` Faltam ${nf(l[pos - 1][1].q - l[pos][1].q + 1)} ${esc(Us(2))} pra passar ${esc(nomeDe(l[pos - 1][0]).split(' ')[0])}.` : ' Segura a liderança.'}</p>` : ''}
    ${l.length ? `<div class="scrollbox">${l.map(([e, x], i) => `<div class="rr ${e === me.email ? 'me' : ''}" style="cursor:default"><i class="${i < 3 ? 'pod' : ''}">${medal(i)}</i><span class="n">${esc(nomeDe(e))}${e === me.email ? ' (você)' : ''}</span><span class="v">${nf(x.q)} ${esc(Us(x.q))}</span><div class="tr"><div style="width:${(x.q / mx * 100).toFixed(0)}%"></div></div><span class="pl" style="grid-column:2/4">${x.n} ${x.n === 1 ? 'venda' : 'vendas'} · ${x.c} ${x.c === 1 ? 'ponto novo' : 'pontos novos'}</span></div>`).join('')}</div>` : '<p class="pl">Ninguém vendeu este mês ainda. Sai na frente!</p>'}</div>
   <div class="rk"><h3>Movimento da equipe</h3>${ev.length ? `<div class="scrollbox">${ev.map(x => `<div class="fd"><div><b>${esc((x.e === me.email ? 'Você' : nomeDe(x.e)).split(' ')[0])}</b> ${esc(x.t)}</div><span class="pl" style="flex:none">${esc(quando(x))}</span></div>`).join('')}</div>` : '<p class="pl">Sem movimento ainda.</p>'}</div>
  </div>` }

/* ---------- início: uma tela para cada papel ---------- */
function vInicio() { if (!can.gest()) return vVendedor(); if (can.dono()) return `<div class="chips switch"><button class="chip ${iv !== 'eu' ? 'on' : ''}" data-act="iv" data-v="emp">Empresa</button><button class="chip ${iv === 'eu' ? 'on' : ''}" data-act="iv" data-v="eu">Minhas vendas</button></div>` + (iv === 'eu' ? vVendedor() : vPainel()); return vPainel() }
function ultimas(email, n) { return peds.filter(o => !email || o.por === email).sort((a, b) => byD(b, a)).slice(0, n) }
function vVendedor() { const pn = (me.nome || '').split(' ')[0], h0 = new Date().getHours(), oi = h0 < 12 ? 'Bom dia' : h0 < 18 ? 'Boa tarde' : 'Boa noite';
  const c = colab(me.email, 'mes'), bv = bonusV(me.email, ymDe('mes')), k = estoqueDe(me.email), meus = meusP().sort((a, b) => a.nome.localeCompare(b.nome)), vis = ilf === 'todos' ? meus : meus.filter(p => p.status === ilf);
  const cob = peds.filter(o => o.por === me.email && o.pg === 'receber' && diasPara(o) !== null && diasPara(o) <= 1).sort((a, b) => a.venc < b.venc ? -1 : 1);
  const rep = meus.filter(p => p.status === 'ativo' && M.get(p.id).prox && M.get(p.id).dAte <= 3).sort((a, b) => M.get(a.id).dAte - M.get(b.id).dAte);
  return `<section class="capa"><div class="capa-t"><span class="pl">${oi},</span><h2>${esc(pn || 'vendedor')}</h2></div>
   <div class="cta"><button class="btn mega" data-w data-act="newPdv"><span class="plus">+</span><span>Cadastrar novo PDV<small>ponto conquistado ou em prospecção</small></span></button>
   <button class="btn mega2" data-w data-act="newPed">Registrar venda ou visita</button></div></section>
  <div class="mets m3"><div class="met"><span class="num">${nf(c.q)}</span><small>${esc(Us(c.q))} vendidas em ${esc(nomeMes(ymDe('mes')))}</small></div><div class="met"><span class="num">${meus.filter(p => p.status === 'ativo').length}</span><small>pontos ativos seus</small></div><div class="met"><span class="num" style="color:${c.venc ? 'var(--brick)' : 'inherit'}">${brl(c.rec)}</span><small>a receber${c.venc ? ` · ${brl(c.venc)} atrasado` : ''}</small></div></div>
  ${cob.length ? `<h3>Cobrar hoje <span>${cob.length}</span></h3><div class="grid">${cob.map(o => cobItem(o, false)).join('')}</div>` : ''}
  <div class="bvcard"><div><span class="pl">Sua meta de ${esc(nomeMes(ymDe('mes')))}</span><div class="bvl">${tierV(bv.nv)}<b>${nf(bv.pts)}</b><span>${esc(Us(bv.pts))} vendidas e pagas</span></div><div class="pl">${progV(bv)}</div>${bv.trava ? `<div class="pl" style="color:var(--brick)">Bônus retido até receber as cobranças atrasadas.</div>` : ''}</div><div class="bvp"><small>bônus do nível</small><b>${esc(cfg.meta.niveis[bv.nv].premio)}</b>${bv.nx ? `<small>próximo: ${esc(bv.nx.premio)}</small>` : ''}</div></div>
  ${k.n ? `<div class="bvcard carga"><div><span class="pl">Mercadoria com você</span><div class="bvl"><b>${nf(k.com)}</b><span>${esc(Us(k.com))} na mão</span></div><div class="pl">Pegou ${nf(k.ent)} · vendeu ${nf(k.vend)} · devolveu ${nf(k.dev)}</div></div><div class="bvr ${k.aPagar > 0 ? 'venc' : ''}"><small>falta acertar com a empresa</small><b>${brl(Math.max(0, k.aPagar))}</b></div></div>` : ''}
  ${rankEquipe()}
  <div class="cols" style="margin-top:12px">
   <div class="rk"><h3>Seus pontos <span>${meus.length}</span></h3>
    <div class="chips" style="margin-bottom:8px">${[['ativo', 'Ativos'], ['prospeccao', 'Prospecção'], ['todos', 'Todos']].map(([kk, t]) => `<button class="chip sm ${ilf === kk ? 'on' : ''}" data-act="ilf" data-v="${kk}">${t} ${kk === 'todos' ? meus.length : meus.filter(p => p.status === kk).length}</button>`).join('')}</div>
    ${vis.length ? `<div class="scrollbox">${vis.map(p => { const s = M.get(p.id); return `<div class="rr" data-act="open" data-id="${esc(p.id)}"><i>•</i><span class="n">${esc(p.nome)}</span><span class="v">${pill(p.status)}</span><span class="pl" style="grid-column:2/4">${esc(lugar(p))}${s?.last ? ' · último pedido ' + fd(s.last.d) : ''}</span></div>` }).join('')}</div>` : `<div class="empty" style="padding:16px">${meus.length ? 'Nenhum ponto nesse filtro.' : 'Nenhum ponto no seu nome ainda. Cada ponto que você cadastrar ou atender entra aqui.'}</div>`}</div>
   <div class="rk">${rep.length ? `<h3>Repor até 3 dias <span>${rep.length}</span></h3>${rep.slice(0, 6).map(p => `<div class="rr" data-act="open" data-id="${esc(p.id)}"><i>!</i><span class="n">${esc(p.nome)}</span><span class="v">${M.get(p.id).dAte < 0 ? 'atrasado ' : ''}${rel(M.get(p.id).dAte)}</span></div>`).join('')}<a class="lk" href="#repor">Ver reposição</a>` : '<h3>Reposição</h3><p class="pl">Nenhum ponto seu pra repor nos próximos 3 dias.</p>'}
    <h3>Suas últimas vendas</h3>${feed(ultimas(me.email, 6), false)}</div>
  </div>` }
function feed(l, comVend) { return l.length ? `<div class="scrollbox">${l.map(o => { const p = pdvs.get(o.pdv);
  return `<div class="fd"><div><b>${esc(p?.nome || 'Ponto removido')}</b><div class="pl">${fd(o.d)}${comVend ? ' · ' + esc(o.pn || nomeDe(o.por)) : ''} · ${nf(o.q)} ${esc(Us(+o.q))} · ${brl(o.v)} · ${o.pg === 'receber' ? `a prazo${o.venc ? ' até ' + fd(o.venc) : ''}` : 'pago'}</div></div><button class="lk" data-act="rec" data-p="${esc(o.pdv)}" data-id="${esc(o.id)}">Comprovante</button></div>` }).join('')}</div>` : '<p class="pl">Nenhuma venda registrada ainda.</p>' }
function vPainel() { const t = today(), T = D(t), PER = { hoje: 'Hoje', sem: '7 dias', mes: 'Este mês' }, k0 = ['hoje', 'sem', 'mes'].includes(ip) ? ip : 'mes';
  const de = k0 === 'hoje' ? t : k0 === 'sem' ? addD(t, -6) : t.slice(0, 8) + '01', ps = peds.filter(o => o.d >= de);
  const rec = peds.filter(o => o.pg === 'receber'), atr = rec.filter(o => diasPara(o) !== null && diasPara(o) < 0), hoje = rec.filter(o => diasPara(o) === 0 || diasPara(o) === 1);
  const recebido = peds.filter(o => o.pg !== 'receber' && (o.pgEm || o.d) >= de).reduce((a, o) => a + (+o.v || 0), 0);
  const repAtr = [...pdvs.values()].filter(p => p.status === 'ativo' && M.get(p.id).prox && M.get(p.id).dAte < 0).length;
  const rua = colabs().map(e => estoqueDe(e)).filter(x => x.n), ruaV = rua.reduce((a, x) => a + Math.max(0, x.aPagar), 0), ruaQ = rua.reduce((a, x) => a + x.com, 0);
  const nfp = peds.filter(o => o.nf && o.nf.st !== 'emitida').length, ver = [...pdvs.values()].filter(p => p.status === 'verificar').length;
  const novos = [...pdvs.values()].filter(p => p.status !== 'fechou' && conqD(p) >= de).length;
  const A = [atr.length && ['cobrar', 'late', brl(atr.reduce((a, o) => a + (+o.v || 0), 0)), `${atr.length} ${atr.length === 1 ? 'cobrança atrasada' : 'cobranças atrasadas'}`],
    hoje.length && ['cobrar', 'hot', hoje.length, `${hoje.length === 1 ? 'pagamento vence' : 'pagamentos vencem'} hoje ou amanhã`],
    repAtr && ['repor', '', repAtr, `${repAtr === 1 ? 'ponto' : 'pontos'} com reposição atrasada`],
    ruaV > 0 && ['time', '', brl(ruaV), `de mercadoria na rua a acertar (${nf(ruaQ)} ${esc(Us(ruaQ))})`],
    can.admin() && nfp && ['notas', '', nfp, `${nfp === 1 ? 'nota fiscal' : 'notas fiscais'} a emitir`],
    ver && ['triagem', '', ver, `${ver === 1 ? 'ponto' : 'pontos'} a verificar`]].filter(Boolean);
  const eq = colabs().map(e => ({ e, c: colab(e, k0 === 'mes' ? 'mes' : 'tudo'), q: ps.filter(o => o.por === e).reduce((a, o) => a + (+o.q || 0), 0), v: ps.filter(o => o.por === e).reduce((a, o) => a + (+o.v || 0), 0), k: estoqueDe(e) })).filter(x => x.q || x.c.rec || x.k.n || acessos.get(x.e)?.ativo).sort((a, b) => b.q - a.q || b.v - a.v);
  const mx = Math.max(1, ...eq.map(x => x.q));
  return `<div class="ptop"><div><h2>Painel de controle</h2><p class="pl">${new Date().toLocaleDateString('pt-BR', { weekday: 'long', day: 'numeric', month: 'long' })}</p></div>${can.gest() ? '<button class="btn sm line xls" data-act="xlsx">Baixar planilha (Excel)</button>' : ''}<div class="cb"><button class="btn sm ink" data-w data-act="newPed">+ Venda ou visita</button><button class="btn sm line" data-w data-act="newPdv">+ Ponto de venda</button></div></div>
  <h3>Precisa de atenção</h3>${A.length ? `<div class="alerts">${A.map(([go, c, n, l]) => `<a class="al ${c}" href="#${go}"><span class="num">${n}</span><small>${l}</small></a>`).join('')}</div>` : '<div class="empty ok">Tudo em dia. Nenhuma cobrança atrasada, nenhuma reposição atrasada.</div>'}
  <div class="ptop" style="margin-top:22px"><h3 style="margin:0">Movimento</h3><div class="chips" style="margin:0">${Object.entries(PER).map(([kk, l]) => `<button class="chip sm ${k0 === kk ? 'on' : ''}" data-act="ip" data-v="${kk}">${l}</button>`).join('')}</div></div>
  <div class="mets m4"><div class="met"><span class="num">${brl(ps.reduce((a, o) => a + (+o.v || 0), 0))}</span><small>vendido · ${ps.length} ${ps.length === 1 ? 'pedido' : 'pedidos'}</small></div><div class="met"><span class="num">${nf(ps.reduce((a, o) => a + (+o.q || 0), 0))}</span><small>${esc(U())}s vendidas</small></div><div class="met"><span class="num">${brl(recebido)}</span><small>recebido</small></div><div class="met"><span class="num">${novos}</span><small>pontos novos</small></div></div>
  ${(() => { const all = [...pdvs.values()].filter(p => p.status !== 'fechou'), q = pq.trim().toLowerCase(), base = all.filter(p => !q || [p.nome, p.bairro, p.cidade, p.resp].join(' ').toLowerCase().includes(q)).sort((a, b) => a.nome.localeCompare(b.nome)), vis = ilf === 'todos' ? base : base.filter(p => p.status === ilf);
    return `<div class="rk" style="margin-top:14px"><div class="ptop"><h3 style="margin:0">Pontos de venda <span>${all.filter(p => p.status === 'ativo').length} ativos</span></h3><input id="pq" type="search" class="pq" placeholder="Buscar ponto, bairro, cidade" value="${esc(pq)}" aria-label="Buscar ponto"></div>
    <div class="chips" style="margin:8px 0">${[['ativo', 'Ativos'], ['prospeccao', 'Prospecção'], ['verificar', 'A verificar'], ['inativo', 'Inativos'], ['todos', 'Todos']].map(([kk, t]) => `<button class="chip sm ${ilf === kk ? 'on' : ''}" data-act="ilf" data-v="${kk}">${t} ${kk === 'todos' ? base.length : base.filter(p => p.status === kk).length}</button>`).join('')}</div>
    ${vis.length ? `<div class="scrollbox">${vis.map(p => { const s = M.get(p.id), c = conquistador(p); return `<div class="rr" data-act="open" data-id="${esc(p.id)}"><i>•</i><span class="n">${esc(p.nome)}</span><span class="v">${pill(p.status)}</span><span class="pl" style="grid-column:2/4">${esc(lugar(p))}${s?.last ? ' · último pedido ' + fd(s.last.d) : ''} · ${c ? 'conquistado por ' + esc(nomeDe(c)) : 'sem vendedor'}</span></div>` }).join('')}</div>` : '<p class="pl">Nenhum ponto nesse filtro.</p>'}</div>` })()}
  <div class="cols" style="margin-top:14px">
   <div class="rk"><h3>Equipe <span>${PER[k0].toLowerCase()}</span></h3>${eq.length ? `<div class="scrollbox">${eq.map(x => `<div class="rr" data-act="colab" data-id="${esc(x.e)}"><i>${esc((nomeDe(x.e)[0] || '?').toUpperCase())}</i><span class="n">${esc(nomeDe(x.e))}</span><span class="v">${nf(x.q)} ${esc(Us(x.q))}</span><div class="tr"><div style="width:${(x.q / mx * 100).toFixed(0)}%"></div></div><span class="pl" style="grid-column:2/4">${x.c.rec ? `a receber ${brl(x.c.rec)}${x.c.venc ? ` (${brl(x.c.venc)} atrasado)` : ''}` : 'nada a receber'}${x.k.n ? ` · com ele ${nf(x.k.com)} ${esc(Us(x.k.com))}` : ''}</span></div>`).join('')}</div>` : '<p class="pl">Ninguém da equipe registrou nada ainda.</p>'}</div>
   <div class="rk"><h3>Últimas vendas</h3>${feed(ultimas('', 30), true)}</div>
  </div>` }

/* ---------- planilha de controle (Excel) ---------- */
async function planilha() {
  if (!navigator.onLine && !window.__xlsx) return toast('Para gerar a planilha precisa de internet na primeira vez.');
  toast('Montando a planilha…');
  let X; try { X = window.__xlsx || await import('https://cdn.sheetjs.com/xlsx-0.20.3/package/xlsx.mjs') } catch { return toast('Não consegui carregar o gerador de planilha. Tente de novo com internet.') }
  const t = today(), e = emp(), pd = o => pdvs.get(o.pdv) || {}, num = v => Math.round((+v || 0) * 100) / 100;
  const pedidos = peds.slice().sort(byD).map(o => { const p = pd(o), d = diasPara(o);
    return { 'Data': o.d, 'Pedido': o.n || o.id, 'Ponto de venda': p.nome || '', 'Cidade': p.cidade || '', 'Vendedor': o.pn || nomeDe(o.por), 'Caixas': num(o.q), 'Subtotal (R$)': num(subtotal(o) || o.v), 'Desconto (R$)': num(o.ds), 'Total (R$)': num(o.v),
      'Condição': o.pg === 'receber' || o.venc ? 'A prazo' : 'À vista', 'Vencimento': o.venc || '', 'Situação': o.pg === 'receber' ? (d !== null && d < 0 ? 'Atrasado' : 'Em aberto') : 'Pago', 'Pago em': o.pg === 'receber' ? '' : (o.pgEm || o.d), 'Forma': o.fp || '', 'Dias de atraso': o.pg === 'receber' && d !== null && d < 0 ? -d : '', 'Lembrete enviado': o.lemb || '', 'NF': o.nf ? (o.nf.st === 'emitida' ? 'Emitida ' + (o.nf.num || '') : 'A emitir') : '' } });
  const itens = []; for (const o of peds.slice().sort(byD)) for (const i of itensDe(o)) itens.push({ 'Data': o.d, 'Pedido': o.n || o.id, 'Ponto de venda': pd(o).nome || '', 'Vendedor': o.pn || nomeDe(o.por), 'Código': i.c, 'Produto': i.d, 'Categoria': prodDe(i.c)?.cat || '', 'Qtd': num(i.q), 'Unidade': i.un || '', 'Preço unit. (R$)': num(i.pu), 'Total (R$)': num(i.q * i.pu) });
  const receber = peds.filter(o => o.pg === 'receber').sort((a, b) => (a.venc || '9') < (b.venc || '9') ? -1 : 1).map(o => { const p = pd(o), d = diasPara(o);
    return { 'Vencimento': o.venc || '', 'Situação': d === null ? 'Sem vencimento' : d < 0 ? `Atrasado ${-d} dias` : d === 0 ? 'Vence hoje' : d === 1 ? 'Vence amanhã' : `Vence em ${d} dias`, 'Ponto de venda': p.nome || '', 'Responsável': p.resp || '', 'WhatsApp': p.contato || '', 'Pedido': o.n || o.id, 'Entregue em': o.d, 'Valor (R$)': num(o.v), 'Vendedor': o.pn || nomeDe(o.por), 'Lembrete enviado': o.lemb || '' } });
  const pontos = [...pdvs.values()].sort((a, b) => a.nome.localeCompare(b.nome)).map(p => { const s = M.get(p.id) || {};
    return { 'Ponto de venda': p.nome, 'Status': ST[p.status] || p.status, 'Tipo': p.tipo || '', 'Responsável': p.resp || '', 'WhatsApp': p.contato || '', 'Bairro': p.bairro || '', 'Cidade': p.cidade || '', 'UF': p.uf || '', 'Endereço': p.endereco || '', 'CPF/CNPJ': p.doc || '', 'Conquistado por': conquistador(p) ? nomeDe(conquistador(p)) : '', 'Nível no clube': s.n ? cfg.clube.niveis[s.nivel]?.nome : '', 'Média caixas/mês': num(s.med), 'Pedidos': s.n || 0, 'Caixas no total': num(s.qtd), 'Total comprado (R$)': num(s.valor), 'A receber (R$)': num(s.receber), 'Último pedido': s.last?.d || '', 'Próxima reposição': s.prox || '' } });
  const ym = ymDe('mes'), equipe = colabs().map(em => { const c = colab(em, 'mes'), b = bonusV(em, ym), k = estoqueDe(em);
    return { 'Colaborador': c.nome, 'Papel': papelNome(acessos.get(em) || (em === me.email ? me : {})), [`Caixas vendidas (${nomeMes(ym)})`]: num(c.q), 'Pedidos no mês': c.n, 'Vendido no mês (R$)': num(c.v), 'A receber (R$)': num(c.rec), 'Atrasado (R$)': num(c.venc), 'Meta: caixas pagas': num(b.pts), 'Nível da meta': cfg.meta.niveis[b.nv].nome, 'Bônus do nível': cfg.meta.niveis[b.nv].premio, 'Bônus retido': b.trava ? 'Sim' : '', 'Bônus pago': b.pago ? `${b.pago.data} ${b.pago.valor || ''}` : '', 'Mercadoria com ele (caixas)': k.n ? num(k.com) : '', 'Mercadoria a acertar (R$)': k.n ? num(Math.max(0, k.aPagar)) : '' } });
  const TT = { e: 'Entrega', d: 'Devolução', p: 'Pagamento' }, mov = cargas.slice().sort((a, b) => a.d < b.d ? -1 : 1).map(m => ({ 'Data': m.d, 'Colaborador': nomeDe(m.em), 'Tipo': TT[m.t], 'Produto': m.t === 'p' ? '' : (prodDe(m.prod)?.d || m.prod), 'Qtd': m.t === 'p' ? '' : num(m.q), 'Valor unit. (R$)': m.t === 'p' ? '' : num(m.pu), 'Valor (R$)': num(m.t === 'p' ? m.v : m.q * m.pu), 'Forma': m.fp || '', 'Obs.': m.o || '' }));
  const resumo = [{ 'Item': 'Empresa', 'Valor': `${e.fantasia} · CNPJ ${e.doc}` }, { 'Item': 'Gerado em', 'Valor': new Date().toLocaleString('pt-BR') }, { 'Item': 'Pontos ativos', 'Valor': [...pdvs.values()].filter(p => p.status === 'ativo').length },
    { 'Item': `Vendido em ${nomeMes(ym)} (R$)`, 'Valor': num(peds.filter(o => o.d.startsWith(ym)).reduce((a, o) => a + (+o.v || 0), 0)) }, { 'Item': `Recebido em ${nomeMes(ym)} (R$)`, 'Valor': num(peds.filter(o => o.pg !== 'receber' && (o.pgEm || o.d).startsWith(ym)).reduce((a, o) => a + (+o.v || 0), 0)) },
    { 'Item': 'A receber hoje (R$)', 'Valor': num(peds.filter(o => o.pg === 'receber').reduce((a, o) => a + (+o.v || 0), 0)) }, { 'Item': 'Atrasado (R$)', 'Valor': num(peds.filter(o => o.pg === 'receber' && diasPara(o) !== null && diasPara(o) < 0).reduce((a, o) => a + (+o.v || 0), 0)) },
    { 'Item': 'Mercadoria com a equipe a acertar (R$)', 'Valor': num(colabs().reduce((a, em) => { const k = estoqueDe(em); return a + (k.n ? Math.max(0, k.aPagar) : 0) }, 0)) }];
  const wb = X.utils.book_new(), add = (nome, rows) => { const ws = X.utils.json_to_sheet(rows.length ? rows : [{ 'Sem registros': '' }]); const ks = Object.keys(rows[0] || { x: '' });
    ws['!cols'] = ks.map(k => ({ wch: Math.min(40, Math.max(k.length + 2, ...rows.slice(0, 200).map(r => String(r[k] ?? '').length + 1))) })); if (rows.length) ws['!autofilter'] = { ref: ws['!ref'] }; X.utils.book_append_sheet(wb, ws, nome) };
  add('Resumo', resumo); add('Pedidos', pedidos); add('Itens vendidos', itens); add('A receber', receber); add('Pontos de venda', pontos); add('Equipe do mês', equipe); add('Mercadoria equipe', mov); add('Produtos', produtos().map(p => ({ 'Código': p.c, 'Produto': p.d, 'Categoria': p.cat || '', 'Unidade': p.un, 'Preço lojista (R$)': num(p.p), 'Sugestão de venda (R$)': num(p.sug), 'NCM': p.ncm || '', 'Conta como caixa': p.f ?? 1, 'À venda': p.ativo === false ? 'Não' : 'Sim' })));
  X.writeFile(wb, `SDF_controle_${t}.xlsx`); toast('Planilha baixada') }

/* ---------- vendedor em lote ---------- */

/* ---------- mercadoria com cada colaborador (consignação) ---------- */
function estoqueDe(email) { const mv = cargas.filter(m => m.em === email), f = m => (+m.q || 0) * (prodDe(m.prod)?.f ?? 1), val = m => (+m.q || 0) * (+m.pu || 0);
  const ini = mv.filter(m => m.t === 'e').map(m => m.d).sort()[0];
  const ent = mv.filter(m => m.t === 'e').reduce((a, m) => a + f(m), 0), entV = mv.filter(m => m.t === 'e').reduce((a, m) => a + val(m), 0);
  const dev = mv.filter(m => m.t === 'd').reduce((a, m) => a + f(m), 0), devV = mv.filter(m => m.t === 'd').reduce((a, m) => a + val(m), 0);
  const pago = mv.filter(m => m.t === 'p').reduce((a, m) => a + (+m.v || 0), 0), ultP = mv.filter(m => m.t === 'p').map(m => m.d).sort().pop() || '';
  const vend = ini ? peds.filter(o => o.por === email && o.d >= ini).reduce((a, o) => a + (+o.q || 0), 0) : 0;
  return { n: mv.length, mv, ent, entV, dev, devV, pago, ultP, vend, com: ent - dev - vend, aPagar: entV - devV - pago, ini } }
function cargaForm(email, t) { const ps = produtos().filter(p => p.ativo !== false), p0 = ps.find(p => +p.f === 1) || ps[0];
  const T = { e: 'Entregar mercadoria', d: 'Registrar devolução', p: 'Receber pagamento' };
  show(`${T[t]} · ${esc(nomeDe(email))}`, `<form class="f" id="cargaF" data-em="${esc(email)}" data-t="${t}">
  ${t === 'p' ? `<label>Valor recebido (R$)<input name="v" type="number" inputmode="decimal" min="0.01" step="0.01" required></label>
   <label>Forma<select name="fp">${FP.map(x => `<option>${x}</option>`).join('')}</select></label>`
  : `<label class="w">Produto<select name="prod" id="cgProd">${ps.map(p => `<option value="${esc(p.c)}" data-p="${+p.p || 0}" ${p === p0 ? 'selected' : ''}>${esc(p.d)}</option>`).join('')}</select></label>
   <label>Quantidade<input name="q" type="number" inputmode="decimal" min="0.5" step="0.5" required></label>
   <label>Valor por unidade (R$)<input name="pu" id="cgPu" type="number" inputmode="decimal" min="0" step="0.01" value="${+p0?.p || 0}"><small>Quanto ${t === 'e' ? 'ele vai pagar' : 'abate da conta dele'} por unidade</small></label>`}
  <label>Data<input name="d" type="date" required value="${today()}"></label>
  <label class="w">Observação<input name="o" placeholder="Opcional"></label>
  <div class="fa w"><button type="button" class="btn line" data-act="colab" data-id="${esc(email)}">Voltar</button><button class="btn ink">Salvar</button></div></form>`);
  $('#cgProd')?.addEventListener('change', e => { $('#cgPu').value = e.target.selectedOptions[0].dataset.p }) }
const salvaCargas = (mov, ok) => fire(setDoc(doc(db, 'config', 'cargas'), { mov, atualizado: today() }), ok);

/* ---------- produtos ---------- */
const CATALOGO_NOV26 = [
  ...[['BAL', 'Do Balão'], ['BOC', 'Da Boca'], ['ES', 'Espírito Santo'], ['QUE', 'Quebradas']].map(([k, n]) => ({ c: 'SDF-DSP-' + k, d: `Display 15 livretos · ${n}`, cat: 'Sedas', un: 'DSP', p: 22, sug: 45.99, ncm: '4813.10.00', f: 1 })),
  ...[['NEU', 'Neutra'], ['ROS', 'Rosa']].map(([k, n]) => ({ c: 'PIT-PAP-' + k, d: `Piteira de papel · ${n}`, cat: 'Piteiras', un: 'UN', p: 1.4, sug: 6, ncm: '', f: 0 })),
  ...[['FLAT', 'Flat'], ['ROUND', 'Round'], ['SLIM', 'Slim']].map(([k, n]) => ({ c: 'PIT-VID-' + k, d: `Piteira de vidro SDF · ${n}`, cat: 'Piteiras', un: 'UN', p: 4.5, sug: 29.99, ncm: '', f: 0 })),
  { c: 'CUIA-SDF', d: 'Cuia SDF (silicone 67 mm)', cat: 'Acessórios', un: 'UN', p: 10.99, sug: 29.99, ncm: '', f: 0 },
  { c: 'CINZ-GOLD', d: 'Cinzeiro SDF Gold', cat: 'Acessórios', un: 'UN', p: 4, sug: 8, ncm: '', f: 0 },
  { c: 'DICH-COCO', d: 'Dichavador fibra de coco', cat: 'Acessórios', un: 'UN', p: 3.5, sug: 15, ncm: '', f: 0 },
  ...[['PRETO', 'Preto SDF'], ['ROSA', 'Rosa SDF'], ['FAVELA', 'Favela SDF']].map(([k, n]) => ({ c: 'ISQ-' + k, d: `Isqueiro fluido · ${n}`, cat: 'Isqueiros', un: 'UN', p: 29.99, sug: 59.99, ncm: '', f: 0 })),
  { c: 'KIT-CHEFE', d: 'Kit do Chefe', cat: 'Kits', un: 'KIT', p: 150, sug: 0, ncm: '', f: 0 },
  { c: 'KIT-CORRE', d: 'Kit do Corre', cat: 'Kits', un: 'KIT', p: 100, sug: 0, ncm: '', f: 0 },
  { c: 'KIT-CRIA', d: 'Kit dos Cria', cat: 'Kits', un: 'KIT', p: 50, sug: 0, ncm: '', f: 0 }];
function vProdutos() { const ps = produtos(), ad = can.admin(), cats = [...new Set(ps.map(p => p.cat || 'Produtos'))], falta = CATALOGO_NOV26.filter(c => !ps.some(p => p.c === c.c)).length;
  return `<h2>Produtos</h2><p class="lead">Tudo que a empresa vende. É essa lista que aparece para escolher no pedido. "Conta como" diz quantas ${esc(U())}s cada unidade vale no giro, nas metas e no bônus (0 para acessórios). NCM e tributação: confirmar com a contabilidade.</p>
  ${ad ? `<div class="cb" style="margin-bottom:16px"><button class="btn ink" data-act="prodNovo">+ Produto</button>${falta ? `<button class="btn line" data-act="prodCat">Carregar os ${falta} produtos do catálogo de novembro</button>` : ''}</div>` : ''}
  ${cats.map(c => `<h3>${esc(c)} <span>${ps.filter(p => (p.cat || 'Produtos') === c).length}</span></h3><table class="stack ptab"><colgroup><col><col style="width:14%"><col style="width:18%"><col style="width:12%"><col style="width:16%"></colgroup><thead><tr><th>Produto</th><th class="r">Lojista</th><th class="r">Sugestão de venda</th><th class="r">Conta como</th><th>Situação</th></tr></thead><tbody>
   ${ps.map((p, k) => [p, k]).filter(([p]) => (p.cat || 'Produtos') === c).map(([p, k]) => `<tr ${ad ? `data-act="prodEd" data-id="${k}" tabindex="0"` : ''}><td><div class="pr"><span class="ph"><img src="${esc(p.foto || 'fotos/' + p.c + '.jpg')}" alt="" loading="lazy" onerror="this.remove()"><i>foto</i></span><div><b>${esc(p.d)}</b><div class="pl">${esc(p.c)} · ${esc(p.un)}${p.ncm ? ' · NCM ' + esc(p.ncm) : ''}</div></div></div></td><td class="r">${brl(p.p)}</td><td class="r">${+p.sug ? brl(p.sug) : ''}</td><td class="r">${nf(p.f ?? 1)}</td><td>${p.ativo === false ? '<span class="pill p-inativo">fora de linha</span>' : '<span class="pill p-ativo">à venda</span>'}</td></tr>`).join('')}</tbody></table>`).join('')}` }
function prodForm(k) { const novo = k === '' || k == null, p = novo ? { c: '', d: '', cat: 'Sedas', un: 'UN', p: 0, sug: 0, ncm: '', f: 0 } : produtos()[+k];
  const cats = [...new Set([...produtos().map(x => x.cat).filter(Boolean), 'Sedas', 'Piteiras', 'Acessórios', 'Isqueiros', 'Kits'])];
  show(novo ? 'Novo produto' : 'Editar produto', `<form class="f" id="prodF2" data-k="${novo ? '' : k}">
  <label class="w">Descrição<input name="d" required value="${esc(p.d)}"></label>
  <label>Código<input name="c" required value="${esc(p.c)}" autocapitalize="characters"></label>
  <label>Categoria<input name="cat" list="catList" value="${esc(p.cat || '')}"><datalist id="catList">${cats.map(c => `<option value="${esc(c)}">`).join('')}</datalist></label>
  <label>Unidade<input name="un" value="${esc(p.un)}" placeholder="UN, DSP, CX, KIT"></label>
  <label>Preço lojista (R$)<input name="p" type="number" step="0.01" min="0" inputmode="decimal" value="${+p.p || 0}"></label>
  <label>Sugestão de venda (R$)<input name="sug" type="number" step="0.01" min="0" inputmode="decimal" value="${+p.sug || ''}"></label>
  <label>Conta como ${esc(U())}s<input name="f" type="number" step="0.01" min="0" inputmode="decimal" value="${p.f ?? 1}"><small>1 para display/caixa de seda, 0 para acessório</small></label>
  <label>NCM<input name="ncm" value="${esc(p.ncm)}"></label>
  <label class="w">Foto<input name="foto" value="${esc(p.foto || '')}" placeholder="vazio: usa fotos/${esc(p.c || 'CODIGO')}.jpg quando a foto for enviada"><small>Mande as fotos com o nome do código (ex.: ${esc(p.c || 'SDF-DSP-BAL')}.jpg) que elas entram no app</small></label>
  <label class="w" style="flex-direction:row;gap:10px;align-items:center"><input type="checkbox" name="ativo" ${p.ativo === false ? '' : 'checked'} style="width:22px;min-height:22px"> À venda (aparece no pedido)</label>
  <div class="fa w">${novo ? '' : `<button type="button" class="btn del" data-act="prodDel" data-id="${k}">Remover</button>`}<button type="button" class="btn line" data-act="close">Cancelar</button><button class="btn ink">Salvar</button></div></form>`) }

/* ---------- desempenho de cada colaborador e bonificação da equipe ---------- */
const MESES = ['janeiro', 'fevereiro', 'março', 'abril', 'maio', 'junho', 'julho', 'agosto', 'setembro', 'outubro', 'novembro', 'dezembro'];
const ymDe = k => { const t = today(); if (k === 'ant') { const [y, m] = t.split('-').map(Number); return m === 1 ? `${y - 1}-12` : `${y}-${String(m - 1).padStart(2, '0')}` } return t.slice(0, 7) };
const nomeMes = ym => MESES[+ym.slice(5, 7) - 1] + (ym.slice(0, 4) === today().slice(0, 4) ? '' : ' de ' + ym.slice(0, 4));
function nivelV(pts) { let n = 0; cfg.meta.niveis.forEach((t, i) => { if (pts >= +t.min) n = i }); return n }
/* meta mensal da equipe: caixas vendidas E recebidas no mês (pela data do pagamento) + ponto novo que recomprou */
function bonusV(email, ym) { const m = cfg.meta, no = d => (d || '').startsWith(ym), t = today();
  const meus = peds.filter(o => o.por === email);
  const cx = meus.filter(o => o.pg !== 'receber' && no(o.pgEm || o.d)).reduce((a, o) => a + (+o.q || 0), 0);
  const pend = meus.filter(o => o.pg === 'receber' && no(o.d)).reduce((a, o) => a + (+o.q || 0), 0);
  const novos = [...pdvs.values()].filter(p => conquistador(p) === email && (M.get(p.id)?.ps || []).length >= 2 && no(M.get(p.id).ps[1].d)).length;
  const trava = meus.filter(o => o.pg === 'receber' && o.venc && D(t) - D(o.venc) > (+m.travaDias || 15));
  const pts = Math.round(cx + novos * (+m.novo || 0)), nv = nivelV(pts), nx = m.niveis[nv + 1];
  const pago = (cfg.pagBV || {})[ym + '|' + email] || null;
  return { cx, pend, novos, pts, nv, nx, falta: nx ? +nx.min - pts : 0, pago, ym, trava: trava.length, travaV: trava.reduce((a, o) => a + (+o.v || 0), 0) } }
const tierV = i => `<span class="tier ${i === 3 ? 't3' : ''}">${esc(cfg.meta.niveis[i]?.nome)}</span>`;
const progV = r => { const b = r.nv ? +cfg.meta.niveis[r.nv].min : 0; return r.nx ? `<span class="prog"><div style="width:${Math.min(100, Math.max(0, (r.pts - b) / (+r.nx.min - b) * 100)).toFixed(0)}%"></div></span>faltam ${nf(r.falta)} ${esc(Us(r.falta))} pra ${esc(r.nx.nome)}` : 'Nível máximo do mês' };
function colabs() { const s = new Set([me.email]); for (const [e, a] of acessos) if (a.papel !== 'leitura') s.add(e);
  peds.forEach(o => o.por && s.add(o.por)); evs.forEach(o => o.por && s.add(o.por)); for (const p of pdvs.values()) { const c = conquistador(p); if (c) s.add(c) } return [...s] }
function colab(email, k) { const de = k === 'mes' ? today().slice(0, 8) + '01' : k === 'ant' ? ymDe('ant') + '-01' : '0000-00-00', ate = k === 'ant' ? ymDe('ant') + '-31' : '9999';
  const em = e => e.por === email && e.d >= de && e.d <= ate, ps = peds.filter(em), vs = evs.filter(e => em(e) && e.t === 'v'), t = today();
  const rec = peds.filter(o => o.por === email && o.pg === 'receber'), venc = rec.filter(o => o.venc && o.venc < t);
  const pts = [...pdvs.values()].filter(p => p.status !== 'fechou' && conquistador(p) === email), novos = pts.filter(p => conqD(p) >= de && conqD(p) <= ate);
  const ult = evs.filter(e => e.por === email).sort((a, b) => byD(b, a))[0];
  return { email, nome: nomeDe(email), papel: acessos.get(email)?.papel || (email === me.email ? me.papel : ''), ativoAc: acessos.get(email)?.ativo !== false,
    q: ps.reduce((a, o) => a + (+o.q || 0), 0), n: ps.length, v: ps.reduce((a, o) => a + (+o.v || 0), 0), vis: vs.length, cli: new Set(ps.map(o => o.pdv)).size,
    rec: rec.reduce((a, o) => a + (+o.v || 0), 0), recN: rec.length, venc: venc.reduce((a, o) => a + (+o.v || 0), 0), pts, novos, at: pts.filter(p => p.status === 'ativo').length,
    nPed: peds.filter(o => o.por === email).length, ult } }
function vTime() {
  if (!can.admin()) return `<div class="empty">Só a administradora vê o desempenho da equipe.</div>`;
  const PER = { mes: 'Este mês', ant: 'Mês passado', tudo: 'Desde o início' }, ym = tp === 'ant' ? ymDe('ant') : ymDe('mes');
  const l = colabs().map(e => ({ ...colab(e, tp), b: bonusV(e, ym) })).filter(c => c.n || c.vis || c.pts.length || c.rec || acessos.has(c.email)).sort((a, b) => b.q - a.q || b.b.pts - a.b.pts);
  const tot = l.reduce((a, c) => ({ q: a.q + c.q, v: a.v + c.v, rec: a.rec + c.rec, venc: a.venc + c.venc, nov: a.nov + c.novos.length }), { q: 0, v: 0, rec: 0, venc: 0, nov: 0 });
  return `<h2>Desempenho da equipe</h2><p class="lead">Tudo que cada colaborador fez na rua: caixas vendidas, pedidos, visitas, pontos no nome dele, o que tem a receber e a bonificação de ${esc(nomeMes(ym))}. Toque numa pessoa para abrir a ficha completa.</p>
  <div class="chips">${Object.entries(PER).map(([k, t]) => `<button class="chip ${tp === k ? 'on' : ''}" data-act="tp" data-v="${k}">${t}</button>`).join('')}</div>
  <div class="mets t5" style="margin-bottom:16px"><div class="met"><span class="num">${nf(tot.q)}</span><small>${esc(U())}s vendidas pela equipe</small></div><div class="met"><span class="num">${brl(tot.v)}</span><small>vendido</small></div><div class="met"><span class="num">${tot.nov}</span><small>pontos conquistados</small></div><div class="met"><span class="num">${brl(tot.rec)}</span><small>a receber hoje</small>${tot.venc ? `<em style="color:var(--brick)">${brl(tot.venc)} vencido</em>` : ''}</div><div class="met"><span class="num">${l.filter(c => c.b.nv > 0).length}</span><small>bateram nível de bônus em ${esc(nomeMes(ym))}</small></div></div>
  ${(() => { const k = l.map(c => ({ c, k: estoqueDe(c.email) })).filter(x => x.k.n); return `<h3>Mercadoria com a equipe <span>caixas que saíram com cada um e o que falta pagar</span></h3>${k.length ? `<table class="stack" style="margin-bottom:18px"><thead><tr><th>Colaborador</th><th class="r">Pegou</th><th class="r">Vendeu</th><th class="r">Devolveu</th><th class="r">Com ele agora</th><th class="r">Falta pagar</th><th>Último acerto</th></tr></thead><tbody>${k.map(({ c, k }) => `<tr data-act="colab" data-id="${esc(c.email)}" tabindex="0"><td><b>${esc(c.nome)}</b></td><td class="r">${nf(k.ent)}</td><td class="r">${nf(k.vend)}</td><td class="r">${nf(k.dev)}</td><td class="r"><b>${nf(k.com)}</b> ${esc(Us(k.com))}</td><td class="r"><b style="color:${k.aPagar > 0 ? 'var(--brick)' : 'inherit'}">${brl(Math.max(0, k.aPagar))}</b>${k.aPagar < 0 ? `<div class="pl">crédito ${brl(-k.aPagar)}</div>` : ''}</td><td>${k.ultP ? fd(k.ultP) : '—'}</td></tr>`).join('')}</tbody><tfoot><tr><td><b>Total na rua</b></td><td></td><td></td><td></td><td class="r"><b>${nf(k.reduce((a, x) => a + x.k.com, 0))}</b></td><td class="r"><b>${brl(k.reduce((a, x) => a + Math.max(0, x.k.aPagar), 0))}</b></td><td></td></tr></tfoot></table>` : `<div class="empty" style="margin-bottom:18px">Nenhuma mercadoria entregue ainda. Abra a ficha do colaborador e toque em "Entregar mercadoria".</div>`}` })()}
  <h3>Colaboradores</h3>
  <div class="grid">${l.map(c => `<button class="card colab" data-act="colab" data-id="${esc(c.email)}">
   <div class="ct"><div><b class="nm" style="cursor:pointer">${esc(c.nome)}</b><div class="pl">${esc(PAPEIS[c.papel] || 'Colaborador')}${c.ativoAc ? '' : ' · acesso desativado'}${c.ult ? ` · ativo ${rel(D(c.ult.d) - D(today()))}` : ' · sem registros'}</div></div><div class="due"><span class="num">${nf(c.q)}</span><small>${esc(Us(c.q))}</small></div></div>
   <div class="meta"><span><b>${c.n}</b> pedidos</span><span><b>${c.vis}</b> visitas</span><span><b>${c.pts.length}</b> pontos dele${c.novos.length ? ` (+${c.novos.length})` : ''}</span><span><b>${brl(c.v)}</b></span></div>
   ${c.rec ? `<div class="meta"><span style="color:${c.venc ? 'var(--brick)' : 'inherit'}">A receber <b style="color:inherit">${brl(c.rec)}</b>${c.venc ? ` · ${brl(c.venc)} vencido` : ''}</span></div>` : ''}
   ${(() => { const k = estoqueDe(c.email); return k.n ? `<div class="meta"><span>Com ele <b>${nf(k.com)}</b> ${esc(Us(k.com))}</span><span style="color:${k.aPagar > 0 ? 'var(--brick)' : 'inherit'}">falta pagar <b style="color:inherit">${brl(Math.max(0, k.aPagar))}</b></span></div>` : '' })()}
   <div class="meta">${tierV(c.b.nv)}<span><b>${nf(c.b.pts)}</b> de meta em ${esc(nomeMes(ym))}</span>${c.b.trava ? '<span class="pill p-verificar">bônus retido</span>' : ''}${c.b.pago ? '<span class="pill p-ativo">bônus pago</span>' : ''}</div></button>`).join('')}</div>
  <h3>Bônus dos vendedores <span>meta do mês · editável em Ajustes</span></h3>
  <div class="tiers">${cfg.meta.niveis.map((t, i) => `<div class="tc ${i === 3 ? 'top3' : ''}"><span class="num">${esc(t.nome)}</span><span class="q">${i ? `a partir de ${+t.min} ${esc(U())}s pagas no mês` : 'abaixo da primeira meta'}</span><span>${esc(t.premio)}</span></div>`).join('')}</div>
  <p class="pl">Conta ${esc(U())}s vendidas e pagas no mês (venda a prazo entra quando for paga). Ponto novo que fez o 2º pedido vale ${+cfg.meta.novo} ${esc(U())}s. O bônus fica retido se o vendedor tiver cobrança vencida há mais de ${+cfg.meta.travaDias} dias.</p>` }
function colabDlg(email) { colabOpen = email; openId = null; const ym = tp === 'ant' ? ymDe('ant') : ymDe('mes'), c = colab(email, tp), b = bonusV(email, ym), t = today();
  const rec = peds.filter(o => o.por === email && o.pg === 'receber').sort((a, b) => (a.venc || a.d) < (b.venc || b.d) ? -1 : 1);
  const at = evs.filter(e => e.por === email).sort((a, b) => byD(b, a)).slice(0, 20);
  const pts = c.pts.slice().sort((a, b) => (M.get(b.id)?.qtd || 0) - (M.get(a.id)?.qtd || 0));
  const PER = { mes: 'este mês', ant: 'mês passado', tudo: 'desde o início' };
  show(esc(c.nome), `<div class="pl">${esc(email)} · ${esc(PAPEIS[c.papel] || 'Colaborador')} · números de ${PER[tp]}</div>
  <div class="stats"><div><span class="num">${nf(c.q)}</span><small>${esc(U())}s vendidas</small></div><div><span class="num">${c.n}</span><small>pedidos (${c.nPed} no total)</small></div><div><span class="num">${c.vis}</span><small>visitas</small></div><div><span class="num">${brl(c.v)}</span><small>vendido</small></div>
  <div><span class="num">${c.pts.length}</span><small>pontos no nome dele</small></div><div><span class="num">${c.at}</span><small>desses ativos</small></div><div><span class="num">${c.novos.length}</span><small>conquistados ${PER[tp]}</small></div><div><span class="num" style="color:${c.venc ? 'var(--brick)' : 'inherit'}">${brl(c.rec)}</span><small>a receber${c.venc ? ` · ${brl(c.venc)} vencido` : ''}</small></div></div>
  ${(() => { const k = estoqueDe(email), T = { e: 'Entregou', d: 'Devolveu', p: 'Pagou' };
   return `<h3>Mercadoria com ele</h3><div class="card"><div class="stats" style="margin:0"><div><span class="num">${nf(k.com)}</span><small>${esc(Us(k.com))} com ele agora</small></div><div><span class="num" style="color:${k.aPagar > 0 ? 'var(--brick)' : 'inherit'}">${brl(Math.max(0, k.aPagar))}</span><small>${k.aPagar < 0 ? `crédito de ${brl(-k.aPagar)}` : 'falta pagar'}</small></div><div><span class="num">${nf(k.ent)}</span><small>pegou${k.ini ? ' desde ' + fd(k.ini) : ''}</small></div><div><span class="num">${nf(k.vend)}</span><small>vendeu (pedidos dele)</small></div></div>
   ${k.com < 0 ? `<div class="flag">Ele registrou mais vendas do que a mercadoria entregue no app. Falta lançar alguma entrega.</div>` : ''}
   <div class="cb" data-adm><button class="btn sm ink" data-act="carga" data-id="${esc(email)}" data-v="e">Entregar mercadoria</button><button class="btn sm sun" data-act="carga" data-id="${esc(email)}" data-v="p">Receber pagamento</button><button class="btn sm line" data-act="carga" data-id="${esc(email)}" data-v="d">Devolução</button></div>
   ${k.n ? `<ul class="hist">${[...k.mv].sort((a, b) => a.d < b.d ? 1 : -1).slice(0, 25).map(m => `<li><span><b>${fd(m.d)}</b> · ${T[m.t]} ${m.t === 'p' ? `<b>${brl(m.v)}</b>${m.fp ? ' · ' + esc(m.fp) : ''}` : `${nf(m.q)} × ${esc(prodDe(m.prod)?.d || m.prod)} · ${brl((+m.q || 0) * (+m.pu || 0))}`}${m.o ? `<br><span class="pl">${esc(m.o)}</span>` : ''}</span><button class="lk" data-adm data-act="delMov" data-id="${esc(m.id)}" data-v="${esc(email)}">Apagar</button></li>`).join('')}</ul>` : '<p class="pl">Nenhuma entrega registrada ainda.</p>'}</div>` })()}
  <h3>Bonificação de ${esc(nomeMes(ym))}</h3>
  <div class="card"><div class="ct bvct"><div>${tierV(b.nv)} <b style="font-size:20px;margin-left:6px">${nf(b.pts)} ${esc(Us(b.pts))}</b><div class="pl" style="margin-top:6px">${progV(b)}</div></div><div class="due"><small>prêmio</small><b style="display:block;max-width:220px">${esc(cfg.meta.niveis[b.nv].premio)}</b></div></div>
   <div class="meta"><span><b>${nf(b.cx)}</b> ${esc(Us(b.cx))} vendidas e pagas</span><span><b>${b.novos}</b> ${b.novos === 1 ? 'ponto novo recomprou' : 'pontos novos recompraram'} × ${+cfg.meta.novo}</span></div>
   ${b.pend ? `<div class="flag">${nf(b.pend)} ${esc(Us(b.pend))} vendidas este mês ainda a receber. Entram na meta quando forem pagas.</div>` : ''}
   ${b.trava ? `<div class="flag" style="color:var(--brick)">Bônus retido: ${b.trava} ${b.trava === 1 ? 'cobrança vencida' : 'cobranças vencidas'} há mais de ${+cfg.meta.travaDias} dias (${brl(b.travaV)}).</div>` : ''}
   <div class="cb">${b.pago ? `<span class="pill p-ativo">Bônus pago em ${fd(b.pago.data)}${b.pago.valor ? ' · ' + esc(b.pago.valor) : ''}</span><button class="lk" data-adm data-act="bvDesfaz" data-id="${esc(email)}" data-v="${ym}">Desfazer</button>` : `<button class="btn sm ink" data-adm data-act="bvPago" data-id="${esc(email)}" data-v="${ym}">Registrar bônus de ${esc(nomeMes(ym))} como pago</button>`}</div></div>
  <h3>A receber <span>${rec.length}</span></h3>${rec.length ? `<ul class="hist">${rec.map(o => { const p = pdvs.get(o.pdv), vc = o.venc && o.venc < t;
    return `<li><span><b>${esc(p?.nome || 'Ponto removido')}</b> · ${brl(o.v)}<br><span class="pl">Pedido ${fd(o.d)}${o.venc ? ` · vence ${fd(o.venc)}` : ''}</span> ${vc ? '<span class="pill p-verificar">vencido</span>' : ''}</span><span><button class="lk" data-w data-act="pago" data-id="${esc(o.id)}" data-p="${esc(o.pdv)}">Marcar pago</button></span></li>` }).join('')}</ul>` : '<p class="pl">Nada a receber.</p>'}
  <h3>Estabelecimentos dele <span>${pts.length}</span></h3>${pts.length ? `<ul class="hist">${pts.map(p => { const s = M.get(p.id);
    return `<li><span><button class="nm" style="font-size:15px" data-act="open" data-id="${esc(p.id)}">${esc(p.nome)}</button><br><span class="pl">${esc(lugar(p))}${s?.last ? ` · último pedido ${fd(s.last.d)}` : ''}${s?.qtd ? ` · ${nf(s.qtd)} ${esc(Us(s.qtd))} no total` : ''}</span></span><span>${pill(p.status)}</span></li>` }).join('')}</ul>` : '<p class="pl">Nenhum ponto no nome dele. Defina em cada ponto, no campo "Conquistado por".</p>'}
  <h3>Atividade recente</h3>${at.length ? `<ul class="hist">${at.map(e => `<li><span><b>${fd(e.d)}</b> · ${esc(pdvs.get(e.pdv)?.nome || 'Ponto removido')}<br><span class="pl">${e.t === 'v' ? 'Visita' : `Pedido de ${nf(e.q)} ${esc(Us(+e.q))}${+e.v ? ' · ' + brl(e.v) : ''}${e.pg === 'receber' ? ' · a receber' : ''}`}${has(e.s) ? ` · sobra ${nf(e.s)}` : ''}</span></span></li>`).join('')}</ul>` : '<p class="pl">Nenhum registro ainda.</p>'}`) }

const V = { inicio: vInicio, cobrar: vCobrar, time: vTime, produtos: vProdutos, notas: vNotas, repor: vRepor, pontos: vPontos, ranking: vRanking, bonus: vBonus, triagem: vTriagem, equipe: vEquipe, ajustes: vAjustes, mais: vMais };
const SO_GEST = ['ranking', 'bonus', 'triagem', 'ajustes', 'notas', 'equipe', 'time', 'produtos'];
const cur = () => { const h = location.hash.slice(1); return V[h] && !(me && !can.gest() && SO_GEST.includes(h)) ? h : 'inicio' };
function render() {
  if (!me || $('#app').hidden) return; derive(); kpis(); const v = cur(); document.body.classList.toggle('v-inicio', v === 'inicio'); if (v === 'inicio' && !render.f) { render.f = 1; document.body.classList.add('first'); setTimeout(() => document.body.classList.remove('first'), 700) }
  const sub = ['ranking', 'triagem', 'equipe', 'ajustes', 'mais', 'notas', 'bonus'].includes(v);
  document.querySelectorAll('#tabs a').forEach(a => { const h = a.getAttribute('href'); a.classList.toggle('on', h === '#' + v || (sub && h === '#mais')) });
  const ae = document.activeElement, id = ae?.id, pos = ae?.selectionStart;
  $('#view').innerHTML = V[v]();
  if (id && $('#view #' + id)) { const e = $('#' + id); e.focus(); try { if (pos != null) e.setSelectionRange(pos, pos) } catch { } }
  if ($('#dlg').open && openId && pdvs.has(openId)) detail(openId); else if ($('#dlg').open && colabOpen) colabDlg(colabOpen);
}

/* ---------- janelas ---------- */
const dlg = $('#dlg');
function show(title, body) { $('#dlgIn').innerHTML = `<div class="dh"><h2>${title}</h2><button class="x" data-act="close" aria-label="Fechar">×</button></div><div class="db">${body}</div>`; if (!dlg.open) dlg.showModal() }
dlg.addEventListener('close', () => { openId = null; colabOpen = null; if (location.hash === '#novo') history.replaceState(null, '', '#inicio') });
function detail(id) { const p = pdvs.get(id); if (!p) return; openId = id; colabOpen = null; const s = M.get(id);
  show(esc(p.nome), `<div class="pl">${esc(lugar(p))}${p.endereco ? ' · ' + esc(p.endereco) : ''}</div>
  <div class="cb" style="margin:10px 0">${pill(p.status)} ${s.n ? tier(s.nivel) + ` <span class="pl">${nf(s.med)} ${esc(Us(s.med))}/mês</span>` : ''} ${p.contato ? `<span class="pill">${esc(p.contato)}</span>` : ''}</div>
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
  <label>Nome do responsável<input name="resp" value="${esc(p.resp)}" placeholder="Quem atende e paga"></label>
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
  const p0 = pdvs.get(pid || ppid), o = oid ? (p0?.hist || []).find(x => x.id === oid) : { t: 'p', d: today(), q: '', pg: (+cfg.prazo || 0) > 0 ? 'receber' : 'pago' };
  if (!o) return; openId = null;
  const st = { pdv: p0?.id || '', t: o.t || 'p' };
  show(oid ? 'Editar registro' : 'Registrar', `<form class="f" data-form="ped" data-id="${esc(oid || '')}">
  <div class="w seg" role="group"><button type="button" data-t="p">Pedido</button><button type="button" data-t="v">Só visita</button></div>
  <div class="w" id="pdvBox"></div>
  <div class="w tp"><b style="font-size:14px">Produtos</b><div id="itBox"></div></div>
  <label>Sobra encontrada no ponto<div class="step"><button type="button" data-inc="s" data-d="-1">−</button><input name="s" type="number" inputmode="decimal" min="0" step="0.5" value="${esc(o.s ?? '')}" placeholder="não contei"><button type="button" data-inc="s" data-d="1">+</button></div><small>Quantas ${esc(U())}s ainda tinham lá. Mede o giro.</small></label>
  <label class="tp">Desconto (R$)<input name="ds" type="number" min="0" step="0.01" inputmode="decimal" value="${esc(o.ds || '')}" placeholder="0,00"></label>
  <label class="tp">Forma de pagamento<select name="fp">${FP.map(x => `<option ${(o.fp || 'PIX') === x ? 'selected' : ''}>${x}</option>`).join('')}</select></label>
  <div class="w tp"><div class="seg" id="pgSeg"><button type="button" data-pg="receber">A prazo</button><button type="button" data-pg="pago">Pago na hora</button></div></div>
  <div class="w tp" id="vencL"><div class="chips" style="margin:0 0 6px">${[7, 15, 21, 30].map(n => `<button type="button" class="chip sm" data-prz="${n}">${n} dias</button>`).join('')}</div><label>Vencimento do pagamento<input name="venc" type="date" value="${esc(o.venc || addD(o.d || today(), +cfg.prazo || 15))}"><small>O ponto paga nesse dia. Na véspera aparece em Cobranças para mandar o lembrete.</small></label></div>
  <div class="w tp tot" id="totBox"></div>
  <label>Data<input name="d" type="date" required value="${esc(o.d)}"></label>
  <label>Observação<input name="o" value="${esc(o.o)}" placeholder="Opcional"></label>
  <div class="fa w"><button class="btn ink" style="flex:1;min-height:54px;font-size:17px">Salvar</button></div></form>`);
  const f = $('#dlgIn form'); f.dataset.pg = o.pg || 'pago'; f.dataset.ppid = ppid || '';
  const its = clone(itensDe(o)); if (!its.length) { const p0 = produtos()[0]; its.push({ c: p0.c, d: p0.d, un: p0.un, ncm: p0.ncm, q: 0, pu: +p0.p || 0 }) }
  f._its = its;
  const paintIts = () => {
    const ps = produtos();
    const cats = [...new Set(ps.filter(p => p.ativo !== false).map(p => p.cat || 'Produtos'))];
    $('#itBox').innerHTML = its.map((i, k) => `<div class="itl"><select data-itp="${k}" aria-label="Produto">${cats.map(c => `<optgroup label="${esc(c)}">${ps.filter(p => p.ativo !== false && (p.cat || 'Produtos') === c).map(p => `<option value="${esc(p.c)}" ${p.c === i.c ? 'selected' : ''}>${esc(p.d)}</option>`).join('')}</optgroup>`).join('')}${ps.some(p => p.c === i.c && p.ativo !== false) ? '' : `<option value="${esc(i.c)}" selected>${esc(i.d)}</option>`}</select>
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
  const paintPrz = () => { const n = f.elements.venc.value && f.elements.d.value ? D(f.elements.venc.value) - D(f.elements.d.value) : null; f.querySelectorAll('[data-prz]').forEach(b => b.classList.toggle('on', +b.dataset.prz === n)) };
  f.addEventListener('change', e => { if (e.target.name === 'd' && f.dataset.pg === 'receber' && !oid) { f.elements.venc.value = addD(e.target.value, +cfg.prazo || 15); paintPrz() } if (e.target.name === 'venc') paintPrz() });
  const paint = () => {
    f.dataset.t = st.t; f.dataset.pdv = st.pdv;
    f.querySelectorAll('[data-t]').forEach(b => b.classList.toggle('on', b.dataset.t === st.t));
    f.querySelectorAll('.tp').forEach(x => x.hidden = st.t === 'v');
    f.querySelectorAll('[data-pg]').forEach(b => b.classList.toggle('on', b.dataset.pg === f.dataset.pg));
    $('#vencL').hidden = st.t === 'v' || f.dataset.pg !== 'receber'; paintPrz();
    const p = pdvs.get(st.pdv), box = $('#pdvBox');
    if (p) box.innerHTML = `<div class="chosen"><div><b>${esc(p.nome)}</b><div class="pl">${esc(lugar(p))}</div></div>${oid ? '' : '<button type="button" class="btn sm line" id="pdvTroca">Trocar</button>'}</div>`;
    else { box.innerHTML = `<label>Ponto de venda<input id="pdvQ" type="search" placeholder="Digite o nome, bairro ou cidade" autocomplete="off"></label><div class="pick" id="pdvRes"></div>`; const q = $('#pdvQ'); q.addEventListener('input', find); find(); setTimeout(() => q.focus(), 50) }
    $('#pdvTroca')?.addEventListener('click', () => { st.pdv = ''; paint() });
  };
  const find = () => { const q = ($('#pdvQ')?.value || '').toLowerCase().trim(), all = [...pdvs.values()].filter(p => p.status !== 'fechou'), mine = can.gest() ? all : meusP();
    const l = (q ? (can.gest() || q.length >= 3 ? all : mine).filter(p => [p.nome, p.bairro, p.cidade].join(' ').toLowerCase().includes(q)) : (can.gest() ? all.filter(p => p.status === 'ativo') : mine).sort((a, b) => (M.get(a.id).dAte ?? 1e9) - (M.get(b.id).dAte ?? 1e9))).slice(0, 8);
    $('#pdvRes').innerHTML = l.length ? l.map(p => `<button type="button" data-pick="${esc(p.id)}">${esc(p.nome)}<small>${esc(lugar(p))} · ${esc(ST[p.status])}</small></button>`).join('') : '<p class="pl">Nenhum ponto encontrado. Cadastre em + Ponto.</p>' };
  f.addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    if (b.dataset.t) { st.t = b.dataset.t; paint() }
    if (b.dataset.pg) { f.dataset.pg = b.dataset.pg; paint() }
    if (b.dataset.prz) { f.elements.venc.value = addD(f.elements.d.value || today(), +b.dataset.prz); paintPrz() }
    if (b.dataset.pick) { st.pdv = b.dataset.pick; paint() }
    if (b.dataset.itd != null) { const i = its[+b.dataset.itd]; i.q = Math.max(0, (+i.q || 0) + (+b.dataset.d)); paintIts(); return }
    if (b.dataset.itx != null) { its.splice(+b.dataset.itx, 1); paintIts(); return }
    if (b.dataset.itadd != null) { const p0 = produtos()[0]; its.push({ c: p0.c, d: p0.d, un: p0.un, ncm: p0.ncm, q: 0, pu: +p0.p || 0 }); paintIts(); return }
    if (b.dataset.inc) { const i = f.elements[b.dataset.inc]; i.value = Math.max(0, (+i.value || 0) + (+b.dataset.d)); i.dispatchEvent(new Event('input', { bubbles: true })) }
  });
  paint(); paintIts();
}

/* comprovante de venda (pedido) */
const condPg = o => o.pg === 'receber' ? `A prazo${o.venc ? ` · ${D(o.venc) - D(o.d)} dias · vence ${brD(o.venc)}` : ''}` : `Pago na hora${o.pgEm && o.pgEm !== o.d ? ' em ' + brD(o.pgEm) : ''}`;
function recHTML(p, o) { const e = emp(), its = itensDe(o), sub = subtotal(o), nfo = o.nf, aberto = o.pg === 'receber';
  const L = (k, v) => v ? `<div><span>${k}</span>${esc(v)}</div>` : '';
  return `<div class="rec" id="rec"><div class="rh"><img src="logo.png" alt=""><div><b>COMPROVANTE DE VENDA</b><span>Pedido nº ${esc(o.n || o.id)}</span><span>${brD(o.d)} · vendedor ${esc(o.pn || nomeDe(o.por))}</span></div></div>
  <div class="rb two"><div><h4>Vendedor (empresa)</h4>${L('', e.fantasia)}${e.razao ? L('Razão social', e.razao) : ''}${L('CNPJ', e.doc)}${L('IE', e.ie)}${L('', [e.endereco, e.bairro].filter(Boolean).join(' - '))}${L('', [e.cidade, e.uf].filter(Boolean).join('/') + (e.cep ? ' · CEP ' + e.cep : ''))}${L('', [e.tel, e.email].filter(Boolean).join(' · '))}</div>
  <div><h4>Cliente</h4>${L('', p.razao || p.nome)}${p.razao && p.razao !== p.nome ? L('Ponto', p.nome) : ''}${L('CPF/CNPJ', p.doc)}${L('IE', p.ie)}${L('', p.endereco)}${L('', [p.bairro, [p.cidade, p.uf].filter(Boolean).join('/')].filter(Boolean).join(' · ') + (p.cep ? ' · CEP ' + p.cep : ''))}${L('Contato', p.contato)}</div></div>
  <table class="rt"><thead><tr><th>Produto</th><th class="r">Qtd</th><th class="r">Unit.</th><th class="r">Total</th></tr></thead><tbody>${its.map(i => `<tr><td>${esc(i.d)}<small>${esc(i.c || '')}</small></td><td class="r">${nf(i.q)} ${esc(i.un || '')}</td><td class="r">${brl(i.pu)}</td><td class="r">${brl(i.q * i.pu)}</td></tr>`).join('')}</tbody></table>
  <div class="rs">${o.ds ? `<div><span>Subtotal</span>${brl(sub)}</div><div><span>Desconto</span>- ${brl(o.ds)}</div>` : ''}<div class="big"><span>Total</span>${brl(o.v)}</div></div>
  <div class="rb"><h4>Pagamento</h4>${L('Condição', condPg(o))}${L('Forma', o.fp)}${L('Situação', aberto ? 'Em aberto' : 'Pago')}</div>
  ${aberto ? `<div class="rpix"><b>Pague por PIX até ${o.venc ? brD(o.venc) : 'o vencimento'}</b>${e.pix ? `<div>Chave PIX (${esc(e.pixTipo || 'chave')}): <b>${esc(e.pix)}</b>${e.banco ? ' · ' + esc(e.banco) : ''}</div>` : ''}<div>Favorecido: ${esc(e.fantasia)}${e.razao ? ' · ' + esc(e.razao) : ''}</div><div>CNPJ: ${esc(e.doc)}</div></div>` : ''}
  ${o.o ? `<div class="rb"><h4>Observação</h4><div>${esc(o.o)}</div></div>` : ''}
  <div class="rsig"><div>Recebi a mercadoria acima</div><div class="ln"></div><div class="pl">Nome e assinatura de quem recebeu</div></div>
  <div class="rf">${nfo ? `Nota fiscal: ${nfo.st === 'emitida' ? 'emitida nº ' + esc(nfo.num || '') : 'será emitida e enviada separadamente'}. ` : ''}${esc(e.rodape || 'Este comprovante é um documento de controle da venda e não substitui a nota fiscal.')}<br>${esc([e.insta, e.site].filter(Boolean).join(' · '))}</div></div>` }
function recibo(pid, oid) { const p = pdvs.get(pid), o = (p?.hist || []).find(x => x.id === oid); if (!p || !o) return; openId = null;
  const falta = o.nf && o.nf.st !== 'emitida' ? faltaNF(p) : [], dg = String(p.contato || '').replace(/\D/g, '');
  show('Comprovante de venda', `${recHTML(p, o)}
  ${falta.length ? `<div class="flag noprint" style="margin-top:12px">Para a nota fiscal ainda falta: <b>${falta.map(esc).join(', ')}</b>. <button class="lk" data-act="edit" data-id="${esc(pid)}">Completar cliente</button></div>` : ''}
  <div class="cb noprint" style="margin-top:14px"><button class="btn sun" data-act="recShare" data-p="${esc(pid)}" data-id="${esc(oid)}">Enviar imagem</button>${dg.length >= 10 ? `<button class="btn line" data-act="recWa" data-p="${esc(pid)}" data-id="${esc(oid)}">WhatsApp (texto)</button>` : ''}<button class="btn line" data-act="recPrint">Imprimir / PDF</button>${o.nf && o.nf.st !== 'emitida' ? `<button class="btn line" data-act="notaCopy" data-p="${esc(pid)}" data-id="${esc(oid)}">Copiar dados p/ nota</button>` : ''}<button class="btn line" data-act="open" data-id="${esc(pid)}">Ver ponto</button></div>`) }
function recTexto(p, o) { const e = emp(), its = itensDe(o), ab = o.pg === 'receber';
  return [`*COMPROVANTE DE VENDA · ${e.fantasia}*`, `Pedido nº ${o.n || o.id} · ${brD(o.d)}`, `CNPJ ${e.doc}${e.ie ? ' · IE ' + e.ie : ''}`, `${e.tel}`, '', `*Cliente:* ${p.razao || p.nome}${p.doc ? ' · ' + p.doc : ''}`, '', ...its.map(i => `• ${nf(i.q)} ${i.un || ''} ${i.d} x ${brl(i.pu)} = ${brl(i.q * i.pu)}`), o.ds ? `Desconto: - ${brl(o.ds)}` : '', `*Total: ${brl(o.v)}*`, '',
    `Condição: ${condPg(o)}`, `Forma: ${o.fp || ''}`, ab ? `\n*Pagamento por PIX até ${o.venc ? brD(o.venc) : 'o vencimento'}*${e.pix ? `\nChave PIX (${e.pixTipo || 'chave'}): ${e.pix}${e.banco ? ' · ' + e.banco : ''}` : ''}\nFavorecido: ${e.fantasia} · CNPJ ${e.doc}` : 'Situação: pago', '', `Vendedor: ${o.pn || ''}`, '_Comprovante de controle da venda. Não substitui a nota fiscal._'].filter(x => x !== '').join('\n') }
function notaTexto(p, o) { const its = itensDe(o), L = [];
  L.push('DESTINATÁRIO', `CNPJ/CPF: ${p.doc || '(falta)'}`, `Nome/Razão social: ${p.razao || p.nome}`, `Inscrição estadual: ${p.ie || 'Isento/não contribuinte'}`, `Endereço: ${p.endereco || '(falta)'}`, `Bairro: ${p.bairro || ''}`, `CEP: ${p.cep || '(falta)'}`, `Município/UF: ${p.cidade || ''}/${p.uf || ''}`, `Telefone: ${p.contato || ''}`, `E-mail: ${p.email || ''}`, '', 'PRODUTOS');
  its.forEach((i, k) => L.push(`${k + 1}) ${i.d}`, `   Código: ${i.c || ''} · NCM: ${i.ncm || ''} · Unidade: ${i.un || ''}`, `   Quantidade: ${String(i.q).replace('.', ',')} · Valor unitário: ${(+i.pu).toFixed(2).replace('.', ',')} · Valor total: ${(i.q * i.pu).toFixed(2).replace('.', ',')}`));
  L.push('', `Desconto: ${(+o.ds || 0).toFixed(2).replace('.', ',')}`, `VALOR TOTAL DA NOTA: ${(+o.v).toFixed(2).replace('.', ',')}`, '', 'PAGAMENTO', `Forma: ${o.fp || ''} · ${o.pg === 'receber' ? 'a prazo, vencimento ' + brD(o.venc) : 'à vista'}`, '', 'INFORMAÇÕES COMPLEMENTARES', `Pedido ${o.n || o.id} de ${brD(o.d)}. Vendedor: ${o.pn || ''}.`);
  return L.join('\n') }
async function recImagem(p, o) {
  const W = 1080, P = 64, c = document.createElement('canvas'), x = c.getContext('2d'), e = emp(), its = itensDe(o), rows = [];
  const T = (t, f, col = '#1a1714', a = 'left', gap = 12) => rows.push({ t: String(t ?? ''), f, col, a, gap });
  T('COMPROVANTE DE VENDA', '800 52px "Barlow Condensed"', '#8a0b0b', 'left', 6); T('Nº ' + (o.n || o.id) + '  ·  ' + brD(o.d), '600 30px Barlow', '#1a1714', 'left', 30);
  T('VENDEDOR (EMPRESA)', '700 24px Barlow', '#8a8178', 'left', 4); T(e.fantasia, '600 30px Barlow'); T('CNPJ ' + e.doc + (e.ie ? '  ·  IE ' + e.ie : ''), '400 26px Barlow'); T([e.endereco, e.bairro, e.cidade + '/' + e.uf].filter(Boolean).join(' · '), '400 24px Barlow'); T([e.tel, e.insta].filter(Boolean).join('  ·  '), '400 24px Barlow', '#1a1714', 'left', 26);
  T('CLIENTE', '700 24px Barlow', '#8a8178', 'left', 4); T(p.razao || p.nome, '600 30px Barlow'); if (p.doc) T('CPF/CNPJ ' + p.doc, '400 26px Barlow'); const end = [p.endereco, p.bairro, [p.cidade, p.uf].filter(Boolean).join('/')].filter(Boolean).join(' · '); if (end) T(end, '400 24px Barlow', '#1a1714', 'left', 26);
  T('PRODUTOS', '700 24px Barlow', '#8a8178', 'left', 8);
  its.forEach(i => { T(i.d, '600 28px Barlow', '#1a1714', 'left', 2); T(`${nf(i.q)} ${i.un || ''} x ${brl(i.pu)} = ${brl(i.q * i.pu)}`, '400 26px Barlow', '#1a1714', 'left', 14) });
  if (o.ds) T('Desconto: - ' + brl(o.ds), '400 26px Barlow');
  T('TOTAL ' + brl(o.v), '800 52px "Barlow Condensed"', '#1a1714', 'left', 20);
  T('Condição: ' + condPg(o) + (o.fp ? '  ·  ' + o.fp : ''), '600 26px Barlow'); if (o.pg === 'receber') { T('PAGUE POR PIX ATÉ ' + (o.venc ? brD(o.venc) : 'O VENCIMENTO'), '700 28px Barlow', '#8a0b0b', 'left', 4); if (e.pix) T(`Chave PIX (${e.pixTipo || 'chave'}): ${e.pix}${e.banco ? ' · ' + e.banco : ''}`, '600 26px Barlow'); T('Favorecido: ' + e.fantasia + ' · CNPJ ' + e.doc, '400 24px Barlow', '#1a1714', 'left', 14) }
  T('Vendedor: ' + (o.pn || ''), '400 24px Barlow', '#1a1714', 'left', 28); T('Comprovante de controle da venda. Não substitui a nota fiscal.', 'italic 400 22px Barlow', '#8a8178');
  let h = P + 200; x.font = '10px Barlow'; for (const r of rows) h += parseInt(r.f.match(/(\d+)px/)[1]) * 1.25 + r.gap; c.width = W; c.height = h + P;
  x.fillStyle = '#fff'; x.fillRect(0, 0, W, c.height); x.fillStyle = '#8a0b0b'; x.fillRect(0, 0, W, 14);
  try { await document.fonts.ready; const img = new Image(); img.src = 'logo.png'; await img.decode(); const s = 170 / img.height; x.drawImage(img, W - P - img.width * s, P - 10, img.width * s, 170) } catch { }
  let y = P + 10; for (const r of rows) { const sz = parseInt(r.f.match(/(\d+)px/)[1]); x.font = r.f; x.fillStyle = r.col; x.textBaseline = 'top'; let t = r.t; while (x.measureText(t).width > W - 2 * P - (y < P + 180 ? 200 : 0) && t.length > 4) t = t.slice(0, -2); if (t !== r.t) t = t.slice(0, -1) + '…'; x.fillText(t, P, y); y += sz * 1.25 + r.gap }
  return new Promise(r => c.toBlob(r, 'image/png')) }

function bonForm(id) { const p = pdvs.get(id), s = M.get(id); openId = null;
  show('Registrar bonificação', `<form class="f" data-form="bon" data-id="${esc(id)}"><p class="w"><b>${esc(p.nome)}</b> está no nível ${tier(s.nivel)} (${nf(s.med)} ${esc(Us(s.med))}/mês).</p>
  <label class="w">O que foi entregue<input name="desc" required value="${esc(cfg.clube.niveis[s.nivel].ben)}"></label><label>Data<input name="data" type="date" value="${today()}"></label>
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
  if (f.id === 'cfgF') { const c = { ...cfg, unidade: v.unidade.trim() || 'caixa', preco: +v.preco || 0, ciclo: +v.ciclo || 15, prazo: +v.prazo || 0,
      clube: { ind: (v.cind || '').trim(), niveis: cfg.clube.niveis.map((_, i) => ({ nome: v['cn' + i].trim(), med: i ? +v['cm' + i] || 0 : 0, meses: i ? +v['cs' + i] || 0 : 0, pont: i ? +v['cp' + i] || 0 : 0, ben: v['cb' + i].trim() })) },
      meta: { novo: +v.mnovo || 0, travaDias: +v.mtrava || 0, niveis: cfg.meta.niveis.map((_, i) => ({ nome: v['vn' + i].trim(), min: i ? +v['vm' + i] || 0 : 0, premio: v['vp' + i].trim() })) } };
    for (let i = 1; i < 4; i++) if (c.meta.niveis[i].min <= c.meta.niveis[i - 1].min) return toast('Na meta da equipe, cada nível precisa de mais caixas que o anterior.');
    for (let i = 2; i < 4; i++) if (c.clube.niveis[i].med < c.clube.niveis[i - 1].med) return toast('No clube, cada nível precisa de média igual ou maior que o anterior.');
    return fire(setDoc(doc(db, 'config', 'geral'), c), 'Ajustes salvos') }
  if (f.id === 'teamF') return addMember(v, f);
  if (f.id === 'cargaF') { const em = f.dataset.em, t = f.dataset.t, m = { id: rid(), em, t, d: v.d, o: (v.o || '').trim(), por: me.email };
    if (t === 'p') Object.assign(m, { v: +v.v || 0, fp: v.fp }); else Object.assign(m, { prod: v.prod, q: +v.q || 0, pu: +v.pu || 0 });
    salvaCargas([...cargas, m], t === 'e' ? 'Entrega registrada' : t === 'p' ? 'Pagamento registrado' : 'Devolução registrada'); cargas = [...cargas, m]; return colabDlg(em) }
  if (f.id === 'prodF2') { const l = clone(produtos()), k = f.dataset.k, p = { c: v.c.trim().toUpperCase(), d: v.d.trim(), cat: (v.cat || '').trim() || 'Produtos', un: (v.un || 'UN').trim().toUpperCase(), p: +v.p || 0, sug: +v.sug || 0, ncm: (v.ncm || '').trim(), f: v.f === '' ? 1 : +v.f, ativo: !!v.ativo, foto: (v.foto || '').trim() };
    if (l.some((x, i) => x.c === p.c && String(i) !== k)) return toast('Já existe um produto com esse código.');
    if (k === '') l.push(p); else l[+k] = p; dlg.close(); return fire(setDoc(doc(db, 'config', 'geral'), { ...cfg, produtos: l }), 'Produto salvo') }
  if (f.id === 'empF') { const e = {}; for (const k of ['fantasia', 'pixTipo', 'banco', 'razao', 'doc', 'ie', 'endereco', 'bairro', 'cidade', 'uf', 'cep', 'tel', 'email', 'pix', 'insta', 'site', 'rodape']) e[k] = (v[k] || '').trim(); e.uf = e.uf.toUpperCase();
    return fire(setDoc(doc(db, 'config', 'geral'), { ...cfg, empresa: e, controlaNF: !!v.controlaNF }), 'Dados da empresa salvos') }
  if (f.id === 'prodF') { const l = produtos().map((_, k) => ({ c: v['c' + k].trim(), d: v['d' + k].trim(), un: (v['un' + k] || 'UN').trim().toUpperCase(), p: +v['p' + k] || 0, ncm: (v['ncm' + k] || '').trim(), f: v['f' + k] === '' ? 1 : +v['f' + k] }));
    if (new Set(l.map(x => x.c)).size !== l.length) return toast('Cada produto precisa de um código diferente.');
    return fire(setDoc(doc(db, 'config', 'geral'), { ...cfg, produtos: l }), 'Produtos salvos') }
  if (f.dataset.form === 'nf') { const p = pdvs.get(f.dataset.p); fire(updateDoc(pref(p.id), { hist: p.hist.map(x => x.id === f.dataset.id ? { ...x, nf: { st: 'emitida', num: v.num.trim(), data: v.data, chave: v.chave.trim() } } : x) }), 'NF-e marcada como emitida'); dlg.close(); return }
  const t = f.dataset.form, id = f.dataset.id;
  if (t === 'pdv') { const ind = v.ind ? byLbl(v.ind) : null;
    const d = { nome: v.nome.trim(), resp: (v.resp || '').trim(), status: v.status, tipo: v.tipo, contato: v.contato.trim(), bairro: v.bairro.trim(), cidade: v.cidade.trim(), uf: v.uf.trim().toUpperCase(), endereco: v.endereco.trim(), redes: v.redes.trim(), doc: v.doc.trim(), razao: v.razao.trim(), ie: v.ie.trim(), cep: v.cep.trim(), email: v.email.trim(), ciclo: +v.ciclo || null, proxContato: v.proxContato || null, indicadoPor: ind && ind.id !== id ? ind.id : null, obs: v.obs.trim(), atualizado: today(), atualizadoPor: me.email };
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
    if (!tv) Object.assign(en, { n: old?.n || numPedido(v.d), it: its, ds, fp: v.fp, venc: f.dataset.pg === 'receber' ? v.venc : null, pgEm: f.dataset.pg === 'receber' ? null : (old?.pgEm || v.d), lemb: old?.lemb || null, nf: old?.nf || (cfg.controlaNF === false ? null : { st: 'pendente' }) });
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
    await setDoc(doc(db, 'acessos', email), { nome: v.nome.trim(), papel: v.papel === 'adminv' ? 'admin' : v.papel, vende: v.papel === 'adminv', ativo: true, criado: today(), criadoPor: me.email });
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
  if (act === 'tp') { tp = v; return render() }
  if (act === 'colab') return colabDlg(id);
  if (act === 'ilf') { ilf = v; return render() }
  if (act === 'xlsx' && can.gest()) return planilha();
  if (act === 'lote' && can.admin()) { const sel = $('#loteV').value, ids = JSON.parse(a.dataset.ids || '[]'); if (!sel) return toast('Escolha o vendedor.'); if (!confirm(`Colocar ${ids.length} ${ids.length === 1 ? 'ponto' : 'pontos'} no nome de ${sel === '-' ? 'ninguém' : nomeDe(sel)}?`)) return; for (let k = 0; k < ids.length; k += 400) { const b = writeBatch(db); ids.slice(k, k + 400).forEach(id => b.update(pref(id), { dono: sel === '-' ? null : sel })); fire(b.commit()) } return toast(`${ids.length} ${ids.length === 1 ? 'ponto atualizado' : 'pontos atualizados'}`) }
  if (act === 'lemb') { const p = pdvs.get(a.dataset.p), o = (p?.hist || []).find(x => x.id === id); if (!o) return; const u = waLink(p, lembreteTexto({ ...o, pdv: p.id })); if (!u) return toast('Esse ponto não tem WhatsApp no cadastro.'); window.open(u, '_blank', 'noopener'); if (can.write()) fire(updateDoc(pref(p.id), { hist: p.hist.map(x => x.id === id ? { ...x, lemb: today() } : x) })); return }
  if (act === 'carga' && can.admin()) return cargaForm(id, v);
  if (act === 'delMov' && can.admin()) { if (!confirm('Apagar este lançamento de mercadoria?')) return; salvaCargas(cargas.filter(m => m.id !== id), 'Lançamento apagado'); return colabDlg(v) }
  if (act === 'prodNovo' && can.admin()) return prodForm('');
  if (act === 'prodEd' && can.admin()) return prodForm(id);
  if (act === 'prodCat' && can.admin()) { const l = clone(produtos()), add = CATALOGO_NOV26.filter(c => !l.some(p => p.c === c.c)); const v0 = l.find(p => p.c === 'SDF-CX'); if (v0) { v0.cat = v0.cat || 'Sedas'; if (add.some(p => p.f === 1)) v0.ativo = false } return fire(setDoc(doc(db, 'config', 'geral'), { ...cfg, produtos: [...l, ...add] }), `${add.length} produtos do catálogo carregados`) }
  if (act === 'bvPago' && can.admin()) { const val = prompt('Valor ou prêmio entregue (opcional):', cfg.meta.niveis[bonusV(id, v).nv].premio) ; if (val === null) return; const m = { ...(cfg.pagBV || {}), [v + '|' + id]: { data: today(), valor: val.trim(), por: me.email, pts: bonusV(id, v).pts } }; return fire(setDoc(doc(db, 'config', 'geral'), { ...cfg, pagBV: m }), 'Bônus registrado como pago') }
  if (act === 'bvDesfaz' && can.admin()) { const m = { ...(cfg.pagBV || {}) }; delete m[v + '|' + id]; return fire(setDoc(doc(db, 'config', 'geral'), { ...cfg, pagBV: m }), 'Registro de bônus desfeito') }
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
  if (act === 'prodDel' && can.admin()) { if (produtos().length < 2) return toast('Precisa ficar pelo menos um produto.'); const l = clone(produtos()); l.splice(+id, 1); if (dlg.open) dlg.close(); return fire(setDoc(doc(db, 'config', 'geral'), { ...cfg, produtos: l }), 'Produto removido') }
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
    if (act === 'pago') return fire(updateDoc(pref(p.id), { hist: p.hist.map(x => x.id === id ? { ...x, pg: 'pago', pgEm: today() } : x) }), 'Pagamento recebido');
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
  if (t.matches('select[data-act=papel]') && can.admin()) return fire(setDoc(doc(db, 'acessos', t.dataset.id), { papel: t.value === 'adminv' ? 'admin' : t.value, vende: t.value === 'adminv' }, { merge: true }), 'Papel alterado');
  if (t.id === 'impF' && t.files[0]) importar(t.files[0]);
});
document.addEventListener('keydown', e => { if (e.key === 'Enter' && e.target.matches('tr[data-act]')) detail(e.target.dataset.id) });
document.addEventListener('input', e => { if (e.target.id === 'pq') { pq = e.target.value; return render() } const m = { fq: 'q', fst: 'st', fcid: 'cid', ftipo: 'tipo', fsort: 'sort', fven: 'ven' }[e.target.id]; if (m) { F[m] = e.target.value; render() } });
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
