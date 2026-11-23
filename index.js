/**
 * haoindex.js — 結合 modvc改ai.py (Python) 與 index.js (Node.js) 兩者優點重寫
 *
 * 採納 Python 版優點:
 *   1. Argo/Xray 端口自動探測 (從 ARGO_PORT 起自動尋找 5 個空閒端口, 避免 3001-3004 衝突)
 *   2. HTTP 主服務端口自動後移 (PORT 被佔用時自動嘗試到 PORT+50)
 *   3. 清理文件時保留 key.txt / cert.pem / private.key (Reality/HY2 重啟後配置不變)
 *   4. SIGINT/SIGTERM 信號處理, 退出時清理全部子進程
 *
 * 採納 Node 版優點:
 *   1. 多下載源自動重試 (主源失敗自動切換備用源) + 臨時文件原子重命名
 *   2. 原生 crypto 生成 X25519 密鑰對 (零外部依賴, 不需要 axios)
 *   3. waitForQuickTunnelLog 帶超時輪詢臨時隧道域名
 *   4. Windows 相容 (taskkill / del) + 根路由支持 index.html 頁面
 *   5. 訂閱路由帶文件讀取兜底
 *
 * 固定隧道模式隱蔽改進:
 *   1. WS 偽裝路徑隨機化 (/vless-argo-<secret> 等), 掃描器無法用公開腳本的已知路徑批量探測
 *   2. 訂閱路徑隨機化 (/sub-<secret>), 防止訂閱被掃描/白嫖 (可用 env SUB_PATH 固定)
 *   3. 未匹配流量回落到本地偽裝網站 — 主動探測只會看到普通網頁, 不暴露異常服務特徵
 *   4. 首頁返回普通 web 服務器默認頁, 移除暴露代理用途的提示文字
 *   5. 偽裝路徑持久化到 paths.txt, 重啟後訂閱鏈接長期有效
 *   6. 三級 DNS 容錯 (公共UDP DNS → DoH直連1.1.1.1 → 系統DNS), 繞過 PaaS 容器 DNS 污染
 *   7. env DL_SOURCE 可追加自建下載源 (如 GitHub raw), 排在最前優先使用
 *   8. /etc/hosts 注入: cloudflared/哪吒等外部二進制走系統 DNS, 把解析出的真實 IP
 *      寫入 /etc/hosts 讓它們繞過容器 DNS 污染 (否則隧道建不起來)
 *   9. cloudflared 邊緣連接固定 --edge-ip-version 4, 避免殘廢 IPv6 導致隧道掛起
 */

const http = require('http');
const https = require('https');
const net = require('net');
const dns = require('dns');
const os = require('os');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { exec } = require('child_process');
const { promisify } = require('util');
const execAsync = promisify(exec);

// ==================== DNS 容錯解析 (部分 PaaS 容器 DNS 被污染, 域名解析成 0.0.0.0 導致 ECONNREFUSED) ====================
// 三級解析: 1) 公共 UDP DNS (8.8.8.8/1.1.1.1) → 2) DoH 加密解析 (直連 1.1.1.1, 不需 DNS) → 3) 系統 DNS
const customResolver = new dns.Resolver({ timeout: 2000, tries: 2 });
customResolver.setServers(['8.8.8.8', '1.1.1.1', '9.9.9.9']);

const dnsCache = new Map();          // 域名解析緩存 (5 分鐘)
const tierFailure = { udp: 0, doh: 0 }; // 連續失敗計數, 超過 2 次自動跳過該級
const DNS_CACHE_TTL = 300000;

function dohResolve(hostname, rrtype, callback) {
  // DoH JSON API, 直連 IP 1.1.1.1 (SNI 偽裝為 cloudflare-dns.com), 完全不依賴容器 DNS
  const req = https.request({
    host: '1.1.1.1',
    servername: 'cloudflare-dns.com',
    path: `/dns-query?name=${encodeURIComponent(hostname)}&type=${rrtype}`,
    method: 'GET',
    headers: { accept: 'application/dns-json', host: 'cloudflare-dns.com' },
    timeout: 5000
  }, (res) => {
    const chunks = [];
    res.on('data', (c) => chunks.push(c));
    res.on('end', () => {
      try {
        const data = JSON.parse(Buffer.concat(chunks).toString());
        const wantType = rrtype === 'A' ? 1 : 28;
        const answers = (data.Answer || []).filter((a) => a.type === wantType).map((a) => a.data);
        callback(null, answers);
      } catch (e) {
        callback(e);
      }
    });
  });
  req.on('timeout', () => req.destroy(new Error('doh timeout')));
  req.on('error', callback);
  req.end();
}

function smartLookup(hostname, options, callback) {
  if (typeof options === 'function') { callback = options; options = {}; }
  options = options || {};
  const all = !!options.all; // Node 20+ autoSelectFamily 需要 all 數組形式回調
  const cacheKey = `${hostname}|${options.family || 0}`;
  const cached = dnsCache.get(cacheKey);
  if (cached && Date.now() < cached.expiry) {
    process.nextTick(() => {
      if (all) callback(null, [{ address: cached.address, family: cached.family }]);
      else callback(null, cached.address, cached.family);
    });
    return;
  }

  const isValidList = (list) => list && list.length > 0 && list[0].address !== '0.0.0.0';
  const finish = (list) => {
    dnsCache.set(cacheKey, { address: list[0].address, family: list[0].family, expiry: Date.now() + DNS_CACHE_TTL });
    if (all) callback(null, list);
    else callback(null, list[0].address, list[0].family);
  };

  const systemFallback = () => {
    dns.lookup(hostname, { family: options.family || 0, all: true }, (err, list) => {
      if (!err && isValidList(list)) finish(list);
      else callback(err || new Error(`ENOTFOUND ${hostname}`));
    });
  };

  const tryDoh = () => {
    if (tierFailure.doh >= 2) return systemFallback();
    const rrtype = options.family === 6 ? 'AAAA' : 'A';
    const family = rrtype === 'A' ? 4 : 6;
    dohResolve(hostname, rrtype, (err, addrs) => {
      if (!err && addrs && addrs.length > 0 && addrs[0] !== '0.0.0.0') {
        tierFailure.doh = 0;
        finish(addrs.map((a) => ({ address: a, family })));
      } else {
        tierFailure.doh += 1;
        systemFallback();
      }
    });
  };

  const tryUdp = (onFail) => {
    if (tierFailure.udp >= 2) return onFail();
    if (options.family === 6) {
      customResolver.resolve6(hostname, (err, addrs) => {
        if (!err && addrs && addrs.length > 0 && addrs[0] !== '0.0.0.0') {
          tierFailure.udp = 0;
          finish(addrs.map((a) => ({ address: a, family: 6 })));
        } else {
          tierFailure.udp += 1;
          onFail();
        }
      });
      return;
    }
    customResolver.resolve4(hostname, (err, addrs) => {
      if (!err && addrs && addrs.length > 0 && addrs[0] !== '0.0.0.0') {
        tierFailure.udp = 0;
        finish(addrs.map((a) => ({ address: a, family: 4 })));
      } else {
        tierFailure.udp += 1;
        if (options.family === 4) return systemFallback();
        onFail();
      }
    });
  };

  tryUdp(tryDoh);
}

// ==================== /etc/hosts 注入: 修復外部進程 (cloudflared/哪吒) 的 DNS 污染 ====================
// 外部二進制使用系統 DNS, 容器 DNS 污染會導致它們無法連接 Cloudflare 邊緣 → 隧道建不起來。
// 把 smartLookup 解析出的真實 IP 寫入 /etc/hosts, 讓外部進程繞過污染。
const HOSTS_FILE = process.platform === 'win32' ? null : '/etc/hosts';
const HOSTS_DOMAINS = [
  'region1.v2.argotunnel.com',   // cloudflared 邊緣 (http2/TLS)
  'region2.v2.argotunnel.com',
  'api.cloudflare.com',          // 隧道註冊 API
  'api.trycloudflare.com',       // 臨時隧道註冊
  'trycloudflare.com'
];

async function fixSystemHosts(extraDomains = []) {
  if (!HOSTS_FILE) return;
  const domains = [...HOSTS_DOMAINS, ...extraDomains].filter(Boolean);
  let hostsContent = '';
  try {
    hostsContent = fs.readFileSync(HOSTS_FILE, 'utf8');
  } catch (e) { /* 文件可能不存在, 繼續嘗試寫入 */ }

  let appended = 0;
  for (const domain of domains) {
    if (hostsContent.includes(` ${domain}`)) continue; // 已有條目, 跳過
    const addr = await new Promise((resolve) => {
      smartLookup(domain, {}, (err, address) => resolve(err ? null : address));
    });
    if (!addr) continue;
    try {
      fs.appendFileSync(HOSTS_FILE, `${addr} ${domain}\n`);
      appended += 1;
    } catch (e) {
      console.log(`/etc/hosts not writable, skip hosts injection: ${e.message}`);
      return;
    }
  }
  if (appended > 0) {
    console.log(`hosts injection: ${appended} entries appended to /etc/hosts`);
  } else {
    console.log('hosts injection: no new entries needed');
  }
}

// ==================== 環境變量配置 ====================
const UPLOAD_URL = process.env.UPLOAD_URL || '';           // 節點或訂閱自動上傳地址
const PROJECT_URL = process.env.PROJECT_URL || '';         // 項目分配的 url, 用於上傳訂閱或保活
const AUTO_ACCESS = (process.env.AUTO_ACCESS || 'false').toLowerCase() === 'true'; // 自動保活開關
const FILE_PATH = process.env.FILE_PATH || '.npm';         // 運行目錄
const SUB_PATH = process.env.SUB_PATH || 'sub';            // 訂閱路徑
const PORT = parseInt(process.env.SERVER_PORT || process.env.PORT || '3000'); // http 訂閱端口
const UUID = process.env.UUID || '';
const NEZHA_SERVER = process.env.NEZHA_SERVER || ''; // 哪吒 v1: nz.abc.com:8008 / v0: nz.abc.com
const NEZHA_PORT = process.env.NEZHA_PORT || '';           // 哪吒 v1 留空, v0 需填寫
const NEZHA_KEY = process.env.NEZHA_KEY || '';
const ARGO_DOMAIN = process.env.ARGO_DOMAIN || '';  // 固定隧道域名, 留空啟用臨時隧道
const ARGO_AUTH = process.env.ARGO_AUTH || '';
const ARGO_PORT = parseInt(process.env.ARGO_PORT || '8001'); // 固定隧道端口
const S5_PORT = process.env.S5_PORT || '';                 // socks5 端口
const HY2_PORT = process.env.HY2_PORT || '';               // hysteria2 端口
const REALITY_PORT = process.env.REALITY_PORT || '';       // reality 端口
const CFIP = process.env.CFIP || 'spring.io';              // 節點優選域名或優選 ip
const CFPORT = parseInt(process.env.CFPORT || '443');      // 優選域名對應端口
const NAME = process.env.NAME || '';                  // 節點名稱
const CHAT_ID = process.env.CHAT_ID || '';       // Telegram chat_id
const BOT_TOKEN = process.env.BOT_TOKEN || ''; // Telegram bot_token
const SHOW_LOG = !['false', 'disable', 'no'].includes((process.env.SHOW_LOG || 'true').toLowerCase());

// ==================== 日誌控制 ====================
if (!SHOW_LOG) {
  console.log = () => {};
  console.error = () => {};
}
function alwaysLog(msg) {
  process.stdout.write(msg + '\n');
}

// ==================== 全局狀態 ====================
let subContent = null;      // 訂閱內容 (base64), 供 http 服務器使用
let privateKey = '';
let publicKey = '';

// ==================== 端口探測 (Python 優點) ====================
// 從 ARGO_PORT 起自動尋找 5 個連續空閒端口, 避免硬編碼 3001-3004 造成的端口衝突
let ARGO_BIND_PORT = ARGO_PORT;
let XRAY_P_VLESS_TCP = ARGO_PORT + 1;
let XRAY_P_VLESS_WS = ARGO_PORT + 2;
let XRAY_P_VMESS_WS = ARGO_PORT + 3;
let XRAY_P_TROJAN_WS = ARGO_PORT + 4;

function tryListen(port) {
  return new Promise((resolve) => {
    const s = net.createServer();
    s.once('error', () => resolve(null));
    s.listen(port, '0.0.0.0', () => resolve(s));
  });
}

async function resolveArgoPorts() {
  for (let base = ARGO_PORT; base + 4 <= 65535; base++) {
    const ports = [base, base + 1, base + 2, base + 3, base + 4];
    const servers = [];
    let allOk = true;
    for (const p of ports) {
      const s = await tryListen(p);
      if (!s) { allOk = false; break; }
      servers.push(s);
    }
    if (allOk) {
      await new Promise((r) => setTimeout(r, 50)); // 等待綁定穩定
      servers.forEach((s) => { try { s.close(); } catch (e) {} });
      if (base !== ARGO_PORT) {
        alwaysLog(`ports ${ARGO_PORT}-${ARGO_PORT + 4} busy, using ${base}-${base + 4}`);
      }
      ARGO_BIND_PORT = base;
      [XRAY_P_VLESS_TCP, XRAY_P_VLESS_WS, XRAY_P_VMESS_WS, XRAY_P_TROJAN_WS] = ports.slice(1);
      return;
    }
    servers.forEach((s) => { try { s.close(); } catch (e) {} });
  }
  throw new Error(`no 5 free ports near ${ARGO_PORT}`);
}

// ==================== 基礎工具 ====================
function isValidPort(port) {
  try {
    if (port === null || port === undefined || port === '') return false;
    if (typeof port === 'string' && port.trim() === '') return false;
    const portNum = parseInt(port);
    if (isNaN(portNum)) return false;
    return portNum >= 1 && portNum <= 65535;
  } catch (error) {
    return false;
  }
}

function generateRandomName(length = 6) {
  const characters = 'abcdefghijklmnopqrstuvwxyz';
  let result = '';
  for (let i = 0; i < length; i++) {
    result += characters.charAt(Math.floor(Math.random() * characters.length));
  }
  return result;
}

// ==================== 原生 HTTP 請求工具 (零依賴, 替代 axios) ====================
function request(url, { method = 'GET', headers = {}, body = null, timeout = 10000 } = {}, redirects = 5) {
  return new Promise((resolve, reject) => {
    let urlObj;
    try { urlObj = new URL(url); } catch (e) { return reject(e); }
    const mod = urlObj.protocol === 'http:' ? http : https;
    const req = mod.request(urlObj, {
      method,
      headers: { 'User-Agent': 'Mozilla/5.0', ...headers },
      timeout,
      lookup: smartLookup // DNS 容錯: 繞過容器 DNS 污染
    }, (res) => {
      if ([301, 302, 303, 307, 308].includes(res.statusCode) && res.headers.location && redirects > 0) {
        res.resume();
        const next = new URL(res.headers.location, urlObj).toString();
        return resolve(request(next, { method, headers, body, timeout }, redirects - 1));
      }
      const chunks = [];
      res.on('data', (c) => chunks.push(c));
      res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, buffer: Buffer.concat(chunks) }));
      res.on('error', reject);
    });
    req.on('timeout', () => req.destroy(new Error('request timeout')));
    req.on('error', reject);
    if (body) req.write(body);
    req.end();
  });
}

async function getJson(url, timeout = 5000) {
  const res = await request(url, { timeout });
  return JSON.parse(res.buffer.toString('utf-8'));
}

async function postJson(url, data, timeout = 10000) {
  const body = JSON.stringify(data);
  return request(url, {
    method: 'POST',
    timeout,
    headers: { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(body) },
    body
  });
}

// ==================== 目錄與路徑 ====================
if (!fs.existsSync(FILE_PATH)) {
  fs.mkdirSync(FILE_PATH, { recursive: true });
}
const workDir = path.resolve(FILE_PATH);

const npmName = generateRandomName();
const webName = generateRandomName();
const botName = generateRandomName();
const phpName = generateRandomName();
const npmPath = path.join(workDir, npmName);
const phpPath = path.join(workDir, phpName);
const webPath = path.join(workDir, webName);
const botPath = path.join(workDir, botName);
const subPath = path.join(workDir, 'sub.txt');
const listPath = path.join(workDir, 'list.txt');
const bootLogPath = path.join(workDir, 'boot.log');
const configPath = path.join(workDir, 'config.json');
const certPath = path.join(workDir, 'cert.pem');
const keyPath = path.join(workDir, 'private.key');
const keyFilePath = path.join(workDir, 'key.txt');
const pathsFilePath = path.join(workDir, 'paths.txt');

// ==================== 隱蔽改進: 偽裝路徑隨機化並持久化 ====================
// 固定隧道模式下, /vless-argo 等是公開腳本的已知特徵路徑, 掃描器可批量探測;
// /sub 默認訂閱路徑太容易被猜中導致節點被白嫖。
// 改進: WS 路徑與訂閱路徑附加隨機 secret, 持久化到 paths.txt (重啟後不變, 訂閱鏈接長期有效)
const ENV_SUB_PATH = (process.env.SUB_PATH || '').trim();
const ENV_PATH_SECRET = (process.env.PATH_SECRET || '').trim();
let SUB_PATH_EFF = 'sub';
let WS_PATH_SECRET = '';

function loadPathSecrets() {
  // 從持久化文件恢復 (優先級低於環境變量)
  if (fs.existsSync(pathsFilePath)) {
    try {
      const content = fs.readFileSync(pathsFilePath, 'utf8');
      const subMatch = content.match(/sub:\s*(\S+)/);
      const secretMatch = content.match(/secret:\s*(\S+)/);
      if (subMatch) SUB_PATH_EFF = subMatch[1];
      if (secretMatch) WS_PATH_SECRET = secretMatch[1];
    } catch (e) { /* 讀取失敗則重新生成 */ }
  }
  if (ENV_SUB_PATH) SUB_PATH_EFF = ENV_SUB_PATH.replace(/^\/+/, '');
  if (ENV_PATH_SECRET) WS_PATH_SECRET = ENV_PATH_SECRET;
  if (!WS_PATH_SECRET) WS_PATH_SECRET = crypto.randomBytes(4).toString('hex');
  // 未顯式指定 SUB_PATH 時, 默認使用隨機訂閱路徑 (防掃描/白嫖)
  if (!ENV_SUB_PATH && (!SUB_PATH_EFF || SUB_PATH_EFF === 'sub')) {
    SUB_PATH_EFF = 'sub-' + crypto.randomBytes(3).toString('hex');
  }
  try {
    fs.writeFileSync(pathsFilePath, `secret: ${WS_PATH_SECRET}\nsub: ${SUB_PATH_EFF}\n`);
  } catch (e) { /* 忽略 */ }
  alwaysLog(`subscription path: /${SUB_PATH_EFF}  (set env SUB_PATH to fix it)`);
}

// 各協議的 WS 偽裝路徑 (帶隨機 secret 後綴, 掃描器無法用已知路徑命中)
function wsPath(proto) {
  return `/${proto}-argo-${WS_PATH_SECRET}`;
}

// ==================== 訂閱器歷史節點刪除 ====================
async function deleteNodes() {
  try {
    if (!UPLOAD_URL) return;
    if (!fs.existsSync(subPath)) return;
    const fileContent = fs.readFileSync(subPath, 'utf-8');
    const decoded = Buffer.from(fileContent, 'base64').toString('utf-8');
    const nodes = decoded.split('\n').filter((line) =>
      /(vless|vmess|trojan|hysteria2|socks):\/\//.test(line)
    );
    if (nodes.length === 0) return;
    await postJson(`${UPLOAD_URL}/api/delete-nodes`, { nodes });
  } catch (err) {
    // 靜默忽略
  }
}

// ==================== 清理歷史文件 (保留 key/cert — Python 優點) ====================
function cleanupOldFiles() {
  try {
    const preserve = new Set([keyFilePath, certPath, keyPath, pathsFilePath]); // 保留 Reality 密鑰、TLS 證書與偽裝路徑
    fs.readdirSync(workDir).forEach((file) => {
      const filePath = path.join(workDir, file);
      if (preserve.has(filePath)) return;
      try {
        const stat = fs.statSync(filePath);
        if (stat.isFile()) fs.rmSync(filePath, { force: true });
      } catch (err) { /* 忽略 */ }
    });
  } catch (err) { /* 忽略 */ }
}

// ==================== X25519 密鑰對 (原生 crypto — Node 優點) ====================
function generateX25519Keypair() {
  const { publicKey: pubKey, privateKey: privKey } = crypto.generateKeyPairSync('x25519');
  const privateKeyRaw = privKey.export({ type: 'pkcs8', format: 'der' }).subarray(-32);
  const publicKeyRaw = pubKey.export({ type: 'spki', format: 'der' }).subarray(-32);
  return {
    privateKey: privateKeyRaw.toString('base64url'),
    publicKey: publicKeyRaw.toString('base64url')
  };
}

function generateOrLoadKeyPair() {
  if (fs.existsSync(keyFilePath)) {
    const content = fs.readFileSync(keyFilePath, 'utf8');
    const privateKeyMatch = content.match(/PrivateKey:\s*(.*)/);
    const publicKeyMatch = content.match(/PublicKey:\s*(.*)/);
    if (privateKeyMatch && publicKeyMatch) {
      privateKey = privateKeyMatch[1].trim();
      publicKey = publicKeyMatch[1].trim();
      console.log('Private Key:', privateKey);
      console.log('Public Key:', publicKey);
      return;
    }
  }
  const keypair = generateX25519Keypair();
  privateKey = keypair.privateKey;
  publicKey = keypair.publicKey;
  fs.writeFileSync(keyFilePath, `PrivateKey: ${privateKey}\nPublicKey: ${publicKey}\n`, 'utf8');
  console.log('Private Key:', privateKey);
  console.log('Public Key:', publicKey);
}

// ==================== TLS 證書生成 (openssl 優先 + 內置兜底) ====================
const FALLBACK_EC_KEY =
  '-----BEGIN EC PARAMETERS-----\n' +
  'BggqhkjOPQMBBw==\n' +
  '-----END EC PARAMETERS-----\n' +
  '-----BEGIN EC PRIVATE KEY-----\n' +
  'MHcCAQEEIM4792SEtPqIt1ywqTd/0bYidBqpYV/++siNnfBYsdUYoAoGCCqGSM49\n' +
  'AwEHoUQDQgAE1kHafPj07rJG+HboH2ekAI4r+e6TL38GWASANnngZreoQDF16ARa\n' +
  '/TsyLyFoPkhLxSbehH/NBEjHtSZGaDhMqQ==\n' +
  '-----END EC PRIVATE KEY-----\n';

const FALLBACK_CERT =
  '-----BEGIN CERTIFICATE-----\n' +
  'MIIBejCCASGgAwIBAgIUfWeQL3556PNJLp/veCFxGNj9crkwCgYIKoZIzj0EAwIw\n' +
  'EzERMA8GA1UEAwwIYmluZy5jb20wHhcNMjUwOTE4MTgyMDIyWhcNMzUwOTE2MTgy\n' +
  'MDIyWjATMREwDwYDVQQDDAhiaW5nLmNvbTBZMBMGByqGSM49AgEGCCqGSM49AwEH\n' +
  'A0IABNZB2nz49O6yRvh26B9npACOK/nuky9/BlgEgDZ54Ga3qEAxdegEWv07Mi8h\n' +
  'aD5IS8Um3oR/zQRIx7UmRmg4TKmjUzBRMB0GA1UdDgQWBBTV1cFID7UISE7PLTBR\n' +
  'BfGbgkrMNzAfBgNVHSMEGDAWgBTV1cFID7UISE7PLTBRBfGbgkrMNzAPBgNVHRMB\n' +
  'Af8EBTADAQH/MAoGCCqGSM49BAMCA0cAMEQCIAIDAJvg0vd/ytrQVvEcSm6XTlB+\n' +
  'eQ6OFb9LbLYL9f+sAiAffoMbi4y/0YUSlTtz7as9S8/lciBF5VCUoVIKS+vX2g==\n' +
  '-----END CERTIFICATE-----\n';

function ensureTlsCertificates() {
  if (fs.existsSync(certPath) && fs.existsSync(keyPath)) return;
  try {
    const { execSync } = require('child_process');
    execSync('openssl version', { stdio: 'ignore' });
    execSync(`openssl ecparam -genkey -name prime256v1 -out "${keyPath}"`, { stdio: 'ignore' });
    execSync(`openssl req -new -x509 -days 3650 -key "${keyPath}" -out "${certPath}" -subj "/CN=bing.com"`, { stdio: 'ignore' });
    return;
  } catch (e) { /* openssl 不可用, 使用內置兜底 */ }
  fs.writeFileSync(keyPath, FALLBACK_EC_KEY);
  fs.writeFileSync(certPath, FALLBACK_CERT);
}

// 計算證書 SHA-256 指紋: openssl 優先, Node crypto 兜底
function getCertificateFingerprint() {
  try {
    const { execSync } = require('child_process');
    const result = execSync(
      `openssl x509 -noout -fingerprint -sha256 -in "${certPath}"`,
      { encoding: 'utf8', timeout: 3000 }
    ).trim();
    const match = result.match(/=(.+)$/);
    if (match && match[1]) return match[1].toUpperCase();
  } catch (e) { /* openssl 不可用 */ }

  try {
    const certData = fs.readFileSync(certPath, 'utf8');
    const derMatch = certData.match(/-----BEGIN CERTIFICATE-----([\s\S]+?)-----END CERTIFICATE-----/);
    if (!derMatch) return '';
    const derBuffer = Buffer.from(derMatch[1].replace(/\s/g, ''), 'base64');
    const hash = crypto.createHash('sha256').update(derBuffer).digest('hex');
    return hash.match(/.{2}/g).join(':').toUpperCase();
  } catch (error) {
    console.error('Failed to calculate certificate fingerprint:', error.message);
    return '';
  }
}

// ==================== Xray 配置生成 (使用自動探測端口 — Python 優點) ====================
function generateConfig() {
  const config = {
    log: { access: '/dev/null', error: '/dev/null', loglevel: 'none' },
    inbounds: [
      {
        tag: 'vless-fallback-in', port: ARGO_BIND_PORT, listen: '::', protocol: 'vless',
        settings: {
          clients: [{ id: UUID, flow: 'xtls-rprx-vision' }],
          decryption: 'none',
          fallbacks: [
            { path: wsPath('vless'), dest: XRAY_P_VLESS_WS },
            { path: wsPath('vmess'), dest: XRAY_P_VMESS_WS },
            { path: wsPath('trojan'), dest: XRAY_P_TROJAN_WS },
            // 未匹配流量回落到本地偽裝網站: 主動探測只會看到普通網頁
            // (替代原裸奔的 vless-tcp 回落, 探測不再暴露異常服務特徵)
            { dest: `127.0.0.1:${httpPort}` }
          ]
        },
        streamSettings: { network: 'tcp' }
      },
      { tag: 'vless-tcp-in', port: XRAY_P_VLESS_TCP, listen: '127.0.0.1', protocol: 'vless', settings: { clients: [{ id: UUID }], decryption: 'none' }, streamSettings: { network: 'tcp', security: 'none' } },
      { tag: 'vless-ws-in', port: XRAY_P_VLESS_WS, listen: '127.0.0.1', protocol: 'vless', settings: { clients: [{ id: UUID, level: 0 }], decryption: 'none' }, streamSettings: { network: 'ws', security: 'none', wsSettings: { path: wsPath('vless') } }, sniffing: { enabled: true, destOverride: ['http', 'tls', 'quic'], metadataOnly: false } },
      { tag: 'vmess-ws-in', port: XRAY_P_VMESS_WS, listen: '127.0.0.1', protocol: 'vmess', settings: { clients: [{ id: UUID, alterId: 0 }] }, streamSettings: { network: 'ws', wsSettings: { path: wsPath('vmess') } }, sniffing: { enabled: true, destOverride: ['http', 'tls', 'quic'], metadataOnly: false } },
      { tag: 'trojan-ws-in', port: XRAY_P_TROJAN_WS, listen: '127.0.0.1', protocol: 'trojan', settings: { clients: [{ password: UUID }] }, streamSettings: { network: 'ws', security: 'none', wsSettings: { path: wsPath('trojan') } }, sniffing: { enabled: true, destOverride: ['http', 'tls', 'quic'], metadataOnly: false } }
    ],
    dns: { servers: ['https+local://8.8.8.8/dns-query'] },
    outbounds: [{ protocol: 'freedom', tag: 'direct' }, { protocol: 'blackhole', tag: 'block' }]
  };

  // VLESS Reality
  if (isValidPort(REALITY_PORT)) {
    config.inbounds.push({
      tag: 'vless-reality-in',
      listen: '::',
      port: parseInt(REALITY_PORT),
      protocol: 'vless',
      settings: {
        clients: [{ id: UUID, flow: 'xtls-rprx-vision' }],
        decryption: 'none'
      },
      streamSettings: {
        network: 'raw',
        security: 'reality',
        realitySettings: {
          show: false,
          dest: 'www.iij.ad.jp:443',
          xver: 0,
          serverNames: ['www.iij.ad.jp'],
          privateKey: privateKey,
          shortIds: ['']
        }
      }
    });
  }

  // Hysteria2
  if (isValidPort(HY2_PORT)) {
    config.inbounds.push({
      tag: 'hysteria-in',
      listen: '::',
      port: parseInt(HY2_PORT),
      protocol: 'hysteria',
      settings: {
        version: 2,
        clients: [{ auth: UUID }]
      },
      streamSettings: {
        network: 'hysteria',
        hysteriaSettings: {
          version: 2,
          masquerade: { type: 'proxy', url: 'https://bing.com' }
        },
        security: 'tls',
        tlsSettings: {
          alpn: ['h3'],
          certificates: [{ certificateFile: certPath, keyFile: keyPath }]
        }
      }
    });
  }

  // SOCKS5
  if (isValidPort(S5_PORT)) {
    config.inbounds.push({
      tag: 's5-in',
      listen: '::',
      port: parseInt(S5_PORT),
      protocol: 'socks',
      settings: {
        auth: 'password',
        accounts: [{ user: UUID.substring(0, 8), pass: UUID.slice(-12) }],
        udp: true
      }
    });
  }

  fs.writeFileSync(configPath, JSON.stringify(config, null, 2));
}

// ==================== 系統架構與多源下載 (Node 優點) ====================
function getSystemArchitecture() {
  const arch = os.arch();
  return (arch === 'arm' || arch === 'arm64' || arch === 'aarch64') ? 'arm' : 'amd';
}

function getFilesForArchitecture(architecture) {
  // 多下載源: 主源失敗自動切換備用源; env DL_SOURCE 可追加自建源 (如 GitHub raw)
  const sources = architecture === 'arm'
    ? ['https://arm64.00666.xyz', 'https://arm64.oooen.com', 'https://arm64.ssss.nyc.mn']
    : ['https://amd64.00666.xyz', 'https://amd64.oooen.com', 'https://amd64.ssss.nyc.mn'];
  const DL_SOURCE = (process.env.DL_SOURCE || '').trim().replace(/\/+$/, '');
  if (DL_SOURCE) sources.unshift(DL_SOURCE);

  const baseFiles = [
    { fileName: webPath, fileUrls: sources.map((s) => `${s}/web`) },
    { fileName: botPath, fileUrls: sources.map((s) => `${s}/bot`) }
  ];

  if (NEZHA_SERVER && NEZHA_KEY) {
    if (NEZHA_PORT) {
      baseFiles.unshift({ fileName: npmPath, fileUrls: sources.map((s) => `${s}/agent`) });
    } else {
      baseFiles.unshift({ fileName: phpPath, fileUrls: sources.map((s) => `${s}/v1`) });
    }
  }

  return baseFiles;
}

// 單文件下載: 臨時文件 + 原子重命名, 支持重定向
function downloadFile(fileName, fileUrl, timeout = 180000) {
  return new Promise((resolve, reject) => {
    let urlObj;
    try { urlObj = new URL(fileUrl); } catch (e) { return reject(e); }
    const mod = urlObj.protocol === 'http:' ? http : https;
    const tmpPath = `${fileName}.download`;
    const req = mod.get(fileUrl, { headers: { 'User-Agent': 'Mozilla/5.0' }, timeout, lookup: smartLookup }, (res) => {
      if ([301, 302, 303, 307, 308].includes(res.statusCode) && res.headers.location) {
        res.resume();
        return resolve(downloadFile(fileName, new URL(res.headers.location, urlObj).toString(), timeout));
      }
      if (res.statusCode !== 200) {
        res.resume();
        return reject(new Error(`HTTP ${res.statusCode}`));
      }
      const writer = fs.createWriteStream(tmpPath);
      res.pipe(writer);
      writer.on('finish', () => writer.close(() => {
        try {
          fs.renameSync(tmpPath, fileName); // 原子重命名, 避免半截文件
          resolve();
        } catch (e) {
          fs.rmSync(tmpPath, { force: true });
          reject(e);
        }
      }));
      writer.on('error', (e) => {
        fs.rmSync(tmpPath, { force: true });
        reject(e);
      });
    });
    req.on('timeout', () => req.destroy(new Error('download timeout')));
    req.on('error', (e) => {
      fs.rmSync(tmpPath, { force: true });
      reject(e);
    });
  });
}

// 帶多源重試的下載
async function downloadWithRetry(fileInfo) {
  for (const url of fileInfo.fileUrls) {
    try {
      await downloadFile(fileInfo.fileName, url);
      console.log(`Download ${path.basename(fileInfo.fileName)} successfully`);
      return;
    } catch (e) {
      console.error(`Download ${path.basename(fileInfo.fileName)} failed from ${new URL(url).host}: ${e.message}`);
    }
  }
  throw new Error(`all sources failed for ${path.basename(fileInfo.fileName)}`);
}

// ==================== 網絡環境診斷: 容器 DNS 是否污染 CF 邊緣, 7844/8443/443 是否可達 ====================
async function netDiagnostics() {
  try {
    if (process.platform === 'win32') return;
    const sysResolve = (host) => new Promise((r) => dns.lookup(host, (err, a) => r(err ? 'ERR:' + (err.code || 'fail') : a)));
    const r1 = await sysResolve('region1.v2.argotunnel.com');
    const r2 = await sysResolve('api.cloudflare.com');
    alwaysLog(`[netdiag] system DNS region1.v2.argotunnel.com => ${r1}`);
    alwaysLog(`[netdiag] system DNS api.cloudflare.com => ${r2}`);
    const tcpTest = (host, port) => new Promise((resolve) => {
      const s = net.connect({ host, port, timeout: 5000 });
      s.on('connect', () => { s.destroy(); resolve('OK'); });
      s.on('timeout', () => { s.destroy(); resolve('TIMEOUT'); });
      s.on('error', (e) => resolve('ERR:' + e.code));
    });
    const t7844 = await tcpTest('198.41.192.7', 7844);
    const t8443 = await tcpTest('198.41.200.13', 8443);
    const t443 = await tcpTest('198.41.192.7', 443);
    alwaysLog(`[netdiag] TCP 198.41.192.7:7844 => ${t7844} | 198.41.200.13:8443 => ${t8443} | 198.41.192.7:443 => ${t443}`);
  } catch (e) {
    alwaysLog('[netdiag] error: ' + e.message);
  }
}

// ==================== 下載並運行所有組件 ====================
async function downloadFilesAndRun() {
  // 網絡診斷
  await netDiagnostics();

  // 先修復外部進程 (cloudflared/哪吒) 的 DNS 污染: 注入 /etc/hosts
  const nezhaHost = NEZHA_SERVER ? NEZHA_SERVER.split(':')[0].replace(/^\[|\]$/g, '') : '';
  await fixSystemHosts(nezhaHost ? [nezhaHost] : []);

  const architecture = getSystemArchitecture();
  const filesToDownload = getFilesForArchitecture(architecture);

  if (filesToDownload.length === 0) {
    console.log(`Can't find a file for the current architecture`);
    return;
  }

  try {
    await Promise.all(filesToDownload.map(downloadWithRetry));
  } catch (err) {
    console.error('Error downloading files:', err.message);
    return;
  }

  // 授權
  const filesToAuthorize = NEZHA_PORT ? [npmPath, webPath, botPath] : [phpPath, webPath, botPath];
  filesToAuthorize.forEach((fp) => {
    if (fs.existsSync(fp)) {
      try {
        fs.chmodSync(fp, 0o775);
        console.log(`Empowerment success for ${path.basename(fp)}: 775`);
      } catch (err) {
        console.error(`Empowerment failed for ${path.basename(fp)}: ${err.message}`);
      }
    }
  });

  // 運行哪吒 (v0: 獨立 agent + config.yaml / v1: 舊版 agent 命令行)
  if (NEZHA_SERVER && NEZHA_KEY) {
    if (!NEZHA_PORT) {
      const port = NEZHA_SERVER.includes(':') ? NEZHA_SERVER.split(':').pop() : '';
      const tlsPorts = new Set(['443', '8443', '2096', '2087', '2083', '2053']);
      const nezhatls = tlsPorts.has(port) ? 'true' : 'false';
      const configYaml = `
client_secret: ${NEZHA_KEY}
debug: false
disable_auto_update: true
disable_command_execute: false
disable_force_update: true
disable_nat: false
disable_send_query: false
gpu: false
insecure_tls: true
ip_report_period: 1800
report_delay: 4
server: ${NEZHA_SERVER}
skip_connection_count: true
skip_procs_count: true
temperature: false
tls: ${nezhatls}
use_gitee_to_upgrade: false
use_ipv6_country_code: false
uuid: ${UUID}`;
      fs.writeFileSync(path.join(workDir, 'config.yaml'), configYaml);
      try {
        await execAsync(`nohup "${phpPath}" -c "${workDir}/config.yaml" >/dev/null 2>&1 &`);
        console.log(`${phpName} is running`);
        await new Promise((r) => setTimeout(r, 1000));
      } catch (error) {
        console.error(`php running error: ${error.message}`);
      }
    } else {
      const tlsPorts = ['443', '8443', '2096', '2087', '2083', '2053'];
      const NEZHA_TLS = tlsPorts.includes(NEZHA_PORT) ? '--tls' : '';
      try {
        await execAsync(`nohup "${npmPath}" -s ${NEZHA_SERVER}:${NEZHA_PORT} -p ${NEZHA_KEY} ${NEZHA_TLS} --disable-auto-update --report-delay 4 --skip-conn --skip-procs >/dev/null 2>&1 &`);
        console.log(`${npmName} is running`);
        await new Promise((r) => setTimeout(r, 1000));
      } catch (error) {
        console.error(`npm running error: ${error.message}`);
      }
    }
  } else {
    console.log('NEZHA variable is empty, skip running');
  }

  // 運行 xray
  try {
    await execAsync(`nohup "${webPath}" -c "${configPath}" >/dev/null 2>&1 &`);
    console.log(`${webName} is running`);
    await new Promise((r) => setTimeout(r, 1000));
  } catch (error) {
    console.error(`web running error: ${error.message}`);
  }

  // 運行 cloudflared
  if (fs.existsSync(botPath)) {
    // 容器 DNS 污染會讓 region*.v2.argotunnel.com 解析成 0.0.0.0, 用 --edge 釘選真實邊緣 IP 直連。
    // 注意: --edge 是 tunnel 級參數, 必須放在 run 子命令之前, 且用重複旗標格式 (--edge IP:7844 --edge IP:7844)
    const EDGE_IPS = (process.env.EDGE_IPS || '').trim().replace(/^--+/, '');
    const DEFAULT_EDGE = '198.41.192.7:7844,198.41.192.67:7844,198.41.192.107:7844,198.41.192.167:7844,198.41.200.13:7844,198.41.200.113:7844,198.41.200.167:7844';
    const edgeArgs = (EDGE_IPS || DEFAULT_EDGE).split(',').filter(Boolean).map((e) => `--edge ${e}`).join(' ');

    let args;
    if (ARGO_AUTH.match(/^[A-Z0-9a-z=]{120,250}$/)) {
      // token 模式也寫日誌, 便於診斷隧道連接問題
      args = `tunnel --edge-ip-version 4 --no-autoupdate --protocol http2 --logfile "${bootLogPath}" --loglevel info ${edgeArgs} run --token ${ARGO_AUTH}`;
    } else if (ARGO_AUTH.match(/TunnelSecret/)) {
      args = `tunnel --edge-ip-version 4 --no-autoupdate --protocol http2 --config "${path.join(workDir, 'tunnel.yml')}" ${edgeArgs} run`;
    } else {
      args = `tunnel --edge-ip-version 4 --no-autoupdate --protocol http2 ${edgeArgs} --logfile "${bootLogPath}" --loglevel info --url http://localhost:${ARGO_BIND_PORT}`;
    }
    try {
      await execAsync(`nohup "${botPath}" ${args} >/dev/null 2>&1 &`);
      console.log(`${botName} is running`);
      await new Promise((r) => setTimeout(r, 2000));
    } catch (error) {
      console.error(`Error executing command: ${error.message}`);
    }
  }

  await new Promise((r) => setTimeout(r, 5000));
}

// ==================== Argo 固定隧道配置 ====================
function argoType() {
  if (!ARGO_AUTH || !ARGO_DOMAIN) {
    console.log('ARGO_DOMAIN or ARGO_AUTH is empty, use quick tunnels');
    return;
  }
  if (ARGO_AUTH.includes('TunnelSecret')) {
    fs.writeFileSync(path.join(workDir, 'tunnel.json'), ARGO_AUTH);
    const tunnelYaml = `
tunnel: ${ARGO_AUTH.split('"')[11]}
credentials-file: ${path.join(workDir, 'tunnel.json')}
protocol: http2

ingress:
  - hostname: ${ARGO_DOMAIN}
    service: http://localhost:${ARGO_BIND_PORT}
    originRequest:
      noTLSVerify: true
  - service: http_status:404
`;
    fs.writeFileSync(path.join(workDir, 'tunnel.yml'), tunnelYaml);
  } else {
    console.log(`Using token connect to tunnel, please set ${ARGO_BIND_PORT} in cloudflare`);
  }
}

// ==================== 獲取臨時隧道域名 (帶超時輪詢 — Node 優點) ====================
async function waitForQuickTunnelLog(timeoutMs = 30000) {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    try {
      if (fs.existsSync(bootLogPath)) {
        const content = fs.readFileSync(bootLogPath, 'utf-8');
        if (/trycloudflare\.com/.test(content)) return content;
      }
    } catch (error) { /* 日誌文件可能仍在創建中 */ }
    await new Promise((r) => setTimeout(r, 1000));
  }
  return '';
}

async function extractDomains(retryCount = 0) {
  let argoDomain;
  if (ARGO_AUTH && ARGO_DOMAIN) {
    argoDomain = ARGO_DOMAIN;
    console.log('ARGO_DOMAIN:', argoDomain);
    await generateLinks(argoDomain);
    return;
  }

  try {
    const fileContent = await waitForQuickTunnelLog();
    const argoDomains = [];
    fileContent.split('\n').forEach((line) => {
      const domainMatch = line.match(/https?:\/\/([^ ]*trycloudflare\.com)\/?/);
      if (domainMatch) argoDomains.push(domainMatch[1]);
    });

    if (argoDomains.length > 0) {
      argoDomain = argoDomains[0];
      console.log('ArgoDomain:', argoDomain);
      await generateLinks(argoDomain);
    } else if (retryCount < 3) { // 限制重試次數, 避免無限遞歸
      console.log('ArgoDomain not found, re-running bot to obtain ArgoDomain');
      try { fs.rmSync(bootLogPath, { force: true }); } catch (e) {}
      try {
        if (process.platform === 'win32') {
          await execAsync(`taskkill /f /im ${botName}.exe > nul 2>&1`);
        } else {
          await execAsync(`pkill -f "[${botName.charAt(0)}]${botName.substring(1)}" > /dev/null 2>&1`);
        }
      } catch (error) { /* 忽略 */ }
      await new Promise((r) => setTimeout(r, 3000));
      const args = `tunnel --edge-ip-version 4 --no-autoupdate --protocol http2 --logfile "${bootLogPath}" --loglevel info --url http://localhost:${ARGO_BIND_PORT}`;
      try {
        await execAsync(`nohup "${botPath}" ${args} >/dev/null 2>&1 &`);
        console.log(`${botName} is running`);
        await new Promise((r) => setTimeout(r, 6000));
        await extractDomains(retryCount + 1);
      } catch (error) {
        console.error(`Error executing command: ${error.message}`);
      }
    } else {
      console.error('Failed to obtain ArgoDomain after 3 retries');
      // 打印 cloudflared 日誌尾部, 便於診斷隧道失敗原因
      try {
        const tail = fs.readFileSync(bootLogPath, 'utf8').split('\n').filter(Boolean).slice(-15).join('\n');
        console.error('--- cloudflared boot.log tail ---\n' + tail);
      } catch (e) { /* boot.log 不存在 */ }
    }
  } catch (error) {
    console.error('Error reading boot.log:', error.message);
  }
}

// ==================== ISP 信息與公網 IP ====================
async function getMetaInfo() {
  try {
    const data = await getJson('https://api.ip.sb/geoip', 3000);
    if (data.country_code && data.isp) {
      return `${data.country_code}-${data.isp}`.replace(/\s+/g, '_');
    }
  } catch (error) { /* 嘗試備用 API */ }
  try {
    const data = await getJson('http://ip-api.com/json', 3000);
    if (data.status === 'success' && data.countryCode && data.org) {
      return `${data.countryCode}-${data.org}`.replace(/\s+/g, '_');
    }
  } catch (error) { /* 忽略 */ }
  return 'Unknown';
}

async function getServerIP() {
  try {
    const res = await request('http://ipv4.ip.sb', { timeout: 3000 });
    return res.buffer.toString().trim();
  } catch (err) {
    try {
      const { execSync } = require('child_process');
      return execSync('curl -sm 3 ipv4.ip.sb').toString().trim();
    } catch (curlErr) {
      try {
        const res = await request('http://ipv6.ip.sb', { timeout: 3000 });
        return `[${res.buffer.toString().trim()}]`;
      } catch (ipv6Err) {
        try {
          const { execSync } = require('child_process');
          return `[${execSync('curl -sm 3 ipv6.ip.sb').toString().trim()}]`;
        } catch (e) {
          console.error('Failed to get IP address:', e.message);
        }
      }
    }
  }
  return '';
}

// ==================== 生成節點訂閱 ====================
async function generateLinks(argoDomain) {
  const ISP = await getMetaInfo();
  const nodeName = NAME ? `${NAME}-${ISP}` : ISP;
  const SERVER_IP = await getServerIP();

  await new Promise((r) => setTimeout(r, 2000));

  const VMESS = {
    v: '2', ps: nodeName, add: CFIP, port: CFPORT, id: UUID, aid: '0',
    scy: 'auto', net: 'ws', type: 'none', host: argoDomain,
    path: wsPath('vmess') + '?ed=2560', tls: 'tls', sni: argoDomain, alpn: '', fp: 'firefox'
  };

  let subTxt = `
vless://${UUID}@${CFIP}:${CFPORT}?encryption=none&security=tls&sni=${argoDomain}&fp=firefox&type=ws&host=${argoDomain}&path=${encodeURIComponent(wsPath('vless') + '?ed=2560')}#${nodeName}

vmess://${Buffer.from(JSON.stringify(VMESS)).toString('base64')}

trojan://${UUID}@${CFIP}:${CFPORT}?security=tls&sni=${argoDomain}&fp=firefox&type=ws&host=${argoDomain}&path=${encodeURIComponent(wsPath('trojan') + '?ed=2560')}#${nodeName}
`;

  // Hysteria2 節點
  if (isValidPort(HY2_PORT)) {
    const fingerprint = getCertificateFingerprint();
    const fingerprintParam = fingerprint ? `&pinSHA256=${encodeURIComponent(fingerprint)}` : '';
    subTxt += `\nhysteria2://${UUID}@${SERVER_IP}:${HY2_PORT}/?sni=www.bing.com&insecure=0&alpn=h3&obfs=none${fingerprintParam}#${nodeName}`;
  }

  // VLESS Reality 節點
  if (isValidPort(REALITY_PORT)) {
    subTxt += `\nvless://${UUID}@${SERVER_IP}:${REALITY_PORT}?encryption=none&flow=xtls-rprx-vision&security=reality&sni=www.iij.ad.jp&fp=firefox&pbk=${publicKey}&type=tcp&headerType=none#${nodeName}`;
  }

  // SOCKS5 節點
  if (isValidPort(S5_PORT)) {
    const S5_AUTH = Buffer.from(`${UUID.substring(0, 8)}:${UUID.slice(-12)}`).toString('base64');
    subTxt += `\nsocks://${S5_AUTH}@${SERVER_IP}:${S5_PORT}#${nodeName}`;
  }

  const subB64 = Buffer.from(subTxt).toString('base64');
  console.log(`\x1b[32m${subB64}\x1b[0m`);
  console.log('\x1b[35mLogs will be deleted in 90 seconds, you can copy the above nodes\x1b[0m');

  fs.writeFileSync(subPath, subB64);
  fs.writeFileSync(listPath, subTxt, 'utf8');
  console.log(`${workDir}/sub.txt saved successfully`);

  subContent = subB64; // 保存到全局變量供 http 服務器使用
  alwaysLog(`subscription: http://${SERVER_IP}:${httpPort}/${SUB_PATH_EFF}`);
}

// ==================== Telegram 推送節點 ====================
async function sendTelegram() {
  if (!BOT_TOKEN || !CHAT_ID) {
    console.log('TG variables is empty, Skipping push nodes to TG');
    return;
  }
  try {
    if (!fs.existsSync(subPath)) {
      console.log('sub.txt not found (nodes not generated), skip TG push');
      return;
    }
    const message = fs.readFileSync(subPath, 'utf8');
    const escapedName = NAME.replace(/[_*[\]()~`>#+=|{}.!-]/g, '\\$&');
    const body = JSON.stringify({
      chat_id: CHAT_ID,
      text: `**${escapedName} Node Update**\n\`\`\`${message}\`\`\``,
      parse_mode: 'MarkdownV2'
    });
    await request(`https://api.telegram.org/bot${BOT_TOKEN}/sendMessage`, {
      method: 'POST',
      timeout: 10000,
      headers: { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(body) },
      body
    });
    console.log('Telegram message sent successfully');
  } catch (error) {
    console.error('Failed to send Telegram message:', error.message);
  }
}

// ==================== 自動上傳節點或訂閱 ====================
async function uploadNodes() {
  if (UPLOAD_URL && PROJECT_URL) {
    try {
      const res = await postJson(`${UPLOAD_URL}/api/add-subscriptions`, {
        subscription: [`${PROJECT_URL}/${SUB_PATH_EFF}`]
      });
      if (res.status === 200) console.log('Subscription uploaded successfully');
    } catch (error) { /* 靜默 */ }
  } else if (UPLOAD_URL) {
    if (!fs.existsSync(listPath)) return;
    const content = fs.readFileSync(listPath, 'utf-8');
    const nodes = content.split('\n').filter((line) =>
      /(vless|vmess|trojan|hysteria2|socks):\/\//.test(line)
    );
    if (nodes.length === 0) return;
    try {
      const res = await postJson(`${UPLOAD_URL}/api/add-nodes`, { nodes });
      if (res.status === 200) console.log('Nodes uploaded successfully');
    } catch (error) { /* 靜默 */ }
  }
}

// ==================== 自動訪問項目 URL (保活) ====================
async function addVisitTask() {
  if (!AUTO_ACCESS || !PROJECT_URL) {
    console.log('Skipping adding automatic access task');
    return;
  }
  try {
    await postJson('https://oooo.serv00.net/add-url', { url: PROJECT_URL });
    console.log('automatic access task added successfully');
  } catch (error) {
    console.error(`Add automatic access task failed: ${error.message}`);
  }
}

// ==================== 90 秒後清理臨時文件 (保留 key/cert — Python 優點) ====================
function cleanFiles() {
  setTimeout(() => {
    // 保留 bootLogPath (cloudflared 日誌, 便於診斷隧道問題) 與 key.txt / cert.pem / private.key
    const filesToDelete = [configPath, listPath, webPath, botPath,
      path.join(workDir, 'tunnel.json'), path.join(workDir, 'tunnel.yml')];
    if (NEZHA_PORT) {
      filesToDelete.push(npmPath);
    } else if (NEZHA_SERVER && NEZHA_KEY) {
      filesToDelete.push(phpPath);
    }
    // 保留 key.txt / cert.pem / private.key, Reality 與 HY2 重啟後配置不變

    filesToDelete.forEach((f) => {
      try { fs.rmSync(f, { force: true }); } catch (e) { /* 忽略 */ }
    });

    try { console.clear(); } catch (e) { /* 忽略 */ }
    alwaysLog('App is running');
    console.log('Thank you for using this script, enjoy!');
  }, 90000);
}

// ==================== 信號處理: 退出時清理子進程 (Python 優點) ====================
async function stopAll() {
  alwaysLog('\nShutting down...');
  try {
    const names = [webName, botName];
    if (NEZHA_PORT) names.push(npmName);
    else if (NEZHA_SERVER && NEZHA_KEY) names.push(phpName);
    for (const name of names) {
      try {
        if (process.platform === 'win32') {
          await execAsync(`taskkill /f /im ${name}.exe > nul 2>&1`);
        } else {
          await execAsync(`pkill -f "[${name.charAt(0)}]${name.substring(1)}" > /dev/null 2>&1`);
        }
      } catch (e) { /* 忽略 */ }
    }
  } catch (e) { /* 忽略 */ }
  setTimeout(() => process.exit(0), 1000);
}
process.on('SIGINT', stopAll);
process.on('SIGTERM', stopAll);

// ==================== 主流程 ====================
async function main() {
  try {
    // Python 優點: 先探測端口再生成配置
    try {
      await resolveArgoPorts();
    } catch (e) {
      alwaysLog(`ERROR: ${e.message}`);
      process.exit(1);
    }

    // 等待 HTTP 端口確定 (xray 未匹配流量回落到偽裝網站需要最終端口)
    await httpReadyPromise;
    loadPathSecrets();

    await deleteNodes();
    cleanupOldFiles();
    argoType();

    // 僅在開啟對應協議時才生成密鑰/證書
    if (isValidPort(REALITY_PORT)) generateOrLoadKeyPair();
    if (isValidPort(HY2_PORT)) ensureTlsCertificates();

    generateConfig();
    await downloadFilesAndRun();
    await extractDomains();
    await sendTelegram();
    await uploadNodes();
    await addVisitTask();
  } catch (error) {
    console.error('Error in main:', error.message);
  }
}

cleanFiles();
main().catch((error) => {
  console.error('Unhandled error in main:', error);
});

// ==================== HTTP 服務器 (端口自動後移 — Python 優點) ====================
let serverPort = PORT;
let httpPort = PORT; // 最終綁定端口, 供 xray 回落使用
let resolveHttpReady;
const httpReadyPromise = new Promise((r) => { resolveHttpReady = r; });

// 偽裝首頁: 看起來像普通的 web 服務器默認頁, 不暴露任何代理特徵
const FAKE_INDEX_HTML = `<!DOCTYPE html>
<html>
<head><meta charset="utf-8"><title>Welcome!</title></head>
<body>
<h1>Welcome!</h1>
<hr>
<p>If you see this page, the web server is successfully installed and working.</p>
<p><em>Powered by WebServer</em></p>
</body>
</html>`;

const server = http.createServer(async (req, res) => {
  const urlPath = req.url.split('?')[0];

  // 訂閱路由: 使用隨機化訂閱路徑 (防掃描/白嫖), 未生成完成時返回與其他路徑一致的 404, 不暴露服務特徵
  if (urlPath === `/${SUB_PATH_EFF}`) {
    if (subContent) {
      res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
      res.end(subContent);
    } else {
      try {
        const fileContent = fs.readFileSync(subPath, 'utf-8');
        res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
        res.end(fileContent);
      } catch (err) {
        res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
        res.end('Not Found');
      }
    }
    return;
  }

  // 根路由: 優先 index.html, 否則返回偽裝頁面 (不再暴露訂閱路徑)
  if (urlPath === '/') {
    try {
      const data = await fs.promises.readFile(path.join(__dirname, 'index.html'), 'utf8');
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
      res.end(data);
    } catch (err) {
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
      res.end(FAKE_INDEX_HTML);
    }
    return;
  }

  res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
  res.end('Not Found');
});

// 端口被佔用時自動後移, 最多嘗試 50 個端口 (Python 優點)
server.on('error', (err) => {
  if (err.code === 'EADDRINUSE' && serverPort < PORT + 50) {
    serverPort += 1;
    server.listen(serverPort);
  } else {
    alwaysLog(`ERROR: all ports ${PORT}-${PORT + 50} are busy or listen failed: ${err.message}`);
    process.exit(1);
  }
});

server.listen(serverPort, () => {
  httpPort = serverPort;
  alwaysLog(`http server is running on ${serverPort}!`);
  resolveHttpReady(serverPort);
});
