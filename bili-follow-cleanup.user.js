// ==UserScript==
// @name         B站关注清理助手
// @name:en      Bilibili Follow Cleanup
// @namespace    https://github.com/HAZBJC/bili-follow-cleanup
// @version      1.1.0
// @description  扫描关注列表，标出「一年未更新」和「已注销」的 UP 主，导出 CSV；确认后再分批取关。默认只读。
// @description:en  Scan your Bilibili following list, flag creators with no uploads for a year and deactivated accounts, export a CSV, then unfollow in controlled batches.
// @author       HAZBJC
// @match        https://space.bilibili.com/*
// @match        https://www.bilibili.com/*
// @grant        none
// @run-at       document-idle
// @homepageURL  https://github.com/HAZBJC/bili-follow-cleanup
// @supportURL   https://github.com/HAZBJC/bili-follow-cleanup/issues
// @updateURL    https://raw.githubusercontent.com/HAZBJC/bili-follow-cleanup/main/bili-follow-cleanup.user.js
// @downloadURL  https://raw.githubusercontent.com/HAZBJC/bili-follow-cleanup/main/bili-follow-cleanup.user.js
// @license      MIT
// ==/UserScript==

(function () {
  'use strict';

  // ============ 配置 ============
  const CFG = {
    pageSize: 50,                 // 关注列表每页拉取数量
    scanDelayMin: 1500,           // 扫描间隔下限（毫秒）
    scanDelayMax: 3200,           // 扫描间隔上限
    unfollowDelayMin: 6000,       // 取关间隔下限
    unfollowDelayMax: 11000,      // 取关间隔上限
    dailyUnfollowCap: 150,        // 每日取关上限（脚本自身限制）
    yearMs: 365 * 24 * 3600 * 1000,
    riskCooldown: 120000,         // 触发风控后冷却时间
  };

  const KEY = 'bili_follow_cleanup_v1';
  const BILI = 'https://api.bilibili.com';

  // ============ 工具 ============
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  const rnd = (a, b) => a + Math.random() * (b - a);

  function fmtDate(ts) {
    if (!ts) return '—';
    const d = new Date(ts * 1000);
    const p = (n) => String(n).padStart(2, '0');
    return `${d.getFullYear()}-${p(d.getMonth() + 1)}-${p(d.getDate())}`;
  }
  function daysAgo(ts) {
    if (!ts) return null;
    return Math.floor((Date.now() - ts * 1000) / 86400000);
  }

  // ---------- MD5（wbi 签名需要） ----------
  const md5 = (function () {
    const S = [7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
      5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
      4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
      6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21];
    const K = [];
    for (let i = 0; i < 64; i++) K[i] = Math.floor(Math.abs(Math.sin(i + 1)) * 4294967296);

    function utf8(str) {
      const out = [];
      for (let i = 0; i < str.length; i++) {
        let c = str.charCodeAt(i);
        if (c < 128) out.push(c);
        else if (c < 2048) out.push(192 | (c >> 6), 128 | (c & 63));
        else if (c < 0xd800 || c >= 0xe000) out.push(224 | (c >> 12), 128 | ((c >> 6) & 63), 128 | (c & 63));
        else {
          i++;
          c = 0x10000 + (((c & 0x3ff) << 10) | (str.charCodeAt(i) & 0x3ff));
          out.push(240 | (c >> 18), 128 | ((c >> 12) & 63), 128 | ((c >> 6) & 63), 128 | (c & 63));
        }
      }
      return out;
    }
    const rotl = (x, c) => (x << c) | (x >>> (32 - c));

    return function (str) {
      const bytes = utf8(str);
      const bitLen = bytes.length * 8;
      bytes.push(0x80);
      while (bytes.length % 64 !== 56) bytes.push(0);
      for (let i = 0; i < 8; i++) bytes.push((Math.floor(bitLen / Math.pow(2, 8 * i))) & 0xff);

      let a0 = 0x67452301, b0 = 0xefcdab89, c0 = 0x98badcfe, d0 = 0x10325476;

      for (let off = 0; off < bytes.length; off += 64) {
        const M = [];
        for (let i = 0; i < 16; i++) {
          M[i] = bytes[off + i * 4] | (bytes[off + i * 4 + 1] << 8) | (bytes[off + i * 4 + 2] << 16) | (bytes[off + i * 4 + 3] << 24);
        }
        let A = a0, B = b0, C = c0, D = d0;
        for (let i = 0; i < 64; i++) {
          let F, g;
          if (i < 16) { F = (B & C) | (~B & D); g = i; }
          else if (i < 32) { F = (D & B) | (~D & C); g = (5 * i + 1) % 16; }
          else if (i < 48) { F = B ^ C ^ D; g = (3 * i + 5) % 16; }
          else { F = C ^ (B | ~D); g = (7 * i) % 16; }
          F = (F + A + K[i] + M[g]) | 0;
          A = D; D = C; C = B;
          B = (B + rotl(F, S[i])) | 0;
        }
        a0 = (a0 + A) | 0; b0 = (b0 + B) | 0; c0 = (c0 + C) | 0; d0 = (d0 + D) | 0;
      }
      const hex = (x) => {
        let s = '';
        for (let i = 0; i < 4; i++) s += ('0' + ((x >>> (8 * i)) & 0xff).toString(16)).slice(-2);
        return s;
      };
      return hex(a0) + hex(b0) + hex(c0) + hex(d0);
    };
  })();

  // ---------- wbi 签名 ----------
  const MIXIN_TAB = [46, 47, 18, 2, 53, 8, 23, 32, 15, 50, 10, 31, 58, 3, 45, 35, 27, 43, 5, 49,
    33, 9, 42, 19, 29, 28, 14, 39, 12, 38, 41, 13, 37, 48, 7, 16, 24, 55, 40, 61,
    26, 17, 0, 1, 60, 51, 30, 4, 22, 25, 54, 21, 56, 59, 6, 63, 57, 62, 11, 36, 20, 34, 44, 52];

  let WBI = { img: '', sub: '', at: 0 };

  async function loadWbi(force) {
    if (!force && WBI.img && Date.now() - WBI.at < 3600e3) return WBI;
    const j = await fetchJson(BILI + '/x/web-interface/nav');
    if (j.code !== 0 || !j.data || !j.data.isLogin) throw new Error('未登录或登录态失效，请先在浏览器登录 B 站');
    const img = j.data.wbi_img.img_url.split('/').pop().split('.')[0];
    const sub = j.data.wbi_img.sub_url.split('/').pop().split('.')[0];
    WBI = { img, sub, at: Date.now() };
    return WBI;
  }

  function signParams(params) {
    const mixin = MIXIN_TAB.map((n) => (WBI.img + WBI.sub)[n]).join('').slice(0, 32);
    const p = Object.assign({}, params, { wts: Math.round(Date.now() / 1000) });
    const query = Object.keys(p).sort().map((k) => {
      const v = String(p[k]).replace(/[!'()*]/g, '');
      return encodeURIComponent(k) + '=' + encodeURIComponent(v);
    }).join('&');
    return query + '&w_rid=' + md5(query + mixin);
  }

  // ---------- 请求 ----------
  class RiskError extends Error {}

  async function fetchJson(url, opts) {
    const res = await fetch(url, Object.assign({ credentials: 'include' }, opts || {}));
    if (res.status === 412) throw new RiskError('HTTP 412（风控拦截）');
    const text = await res.text();
    let j;
    try { j = JSON.parse(text); } catch (e) { throw new Error('返回非 JSON：' + text.slice(0, 120)); }
    if (j && (j.code === -352 || j.code === -412 || j.code === -509 || j.code === -799)) {
      throw new RiskError('风控 code=' + j.code + ' ' + (j.message || ''));
    }
    return j;
  }

  async function getSigned(path, params) {
    await loadWbi();
    return fetchJson(BILI + path + '?' + signParams(params));
  }

  // ============ 状态 ============
  let S = {
    mid: 0,
    total: 0,
    totalPages: 0,
    cursorPage: 1,
    queue: [],
    results: {},
    scanning: false,
    paused: false,
    stopped: false,
    unfollow: { date: '', count: 0 },
    note: '',
  };

  function save() {
    try {
      localStorage.setItem(KEY, JSON.stringify({
        mid: S.mid, total: S.total, totalPages: S.totalPages, cursorPage: S.cursorPage,
        queue: S.queue, results: S.results, unfollow: S.unfollow,
      }));
    } catch (e) { /* 容量问题忽略 */ }
  }
  function load() {
    try {
      const raw = localStorage.getItem(KEY);
      if (!raw) return;
      const o = JSON.parse(raw);
      Object.assign(S, o);
    } catch (e) { /* ignore */ }
  }

  // 已缓存结果的就地修正：B 站注销账号一般不返回 -404，而是保留旧视频列表，
  // 只能靠昵称兜底（「账号已注销」「账号已注销17541」等）。
  const DEAD_NAME = /账号已注销/;
  function normalizeResults() {
    let fixed = 0;
    Object.values(S.results).forEach((r) => {
      if (r && DEAD_NAME.test(r.uname || '') && r.status !== 'deleted') {
        r.status = 'deleted';
        r.note = '名称显示已注销';
        fixed++;
      }
    });
    if (fixed) save();
    return fixed;
  }

  // 本地日期。不能用 toISOString()，那是 UTC，重置点会跑到北京时间早上 8 点。
  const today = () => {
    const d = new Date();
    const p = (n) => String(n).padStart(2, '0');
    return d.getFullYear() + '-' + p(d.getMonth() + 1) + '-' + p(d.getDate());
  };
  function bumpUnfollow() {
    if (S.unfollow.date !== today()) S.unfollow = { date: today(), count: 0 };
    S.unfollow.count++;
    save();
  }

  // ============ 判定 ============
  const isDead = (r) => r.status === 'deleted';
  const isStale = (r) => r.status === 'ok' && r.lastTs && Date.now() - r.lastTs * 1000 > CFG.yearMs;
  const isTarget = (r) => (isDead(r) || isStale(r)) && !r.unfollowed;

  // ============ 扫描 ============
  async function fetchFollowPage(pn) {
    const j = await getSigned('/x/relation/followings', {
      vmid: S.mid, pn, ps: CFG.pageSize, order: 'desc', order_type: 'attention',
    });
    if (j.code !== 0) throw new Error('拉取关注列表失败 code=' + j.code + ' ' + (j.message || ''));
    const list = (j.data && j.data.list) || [];
    if (!S.total) S.total = j.data.total || 0;
    return list;
  }

  async function checkUser(mid, uname) {
    const j = await getSigned('/x/space/wbi/arc/search', { mid, ps: 1, pn: 1, order: 'pubdate' });
    if (j.code === -404) return { mid, uname, status: 'deleted', lastTs: 0 };
    if (j.code !== 0) return { mid, uname, status: 'error', lastTs: 0, note: 'code=' + j.code };
    const vlist = (j.data && j.data.list && j.data.list.vlist) || [];
    // 注销账号往往仍返回旧视频列表，只能靠昵称兜底
    if (/账号已注销/.test(uname || '')) {
      return { mid, uname, status: 'deleted', lastTs: vlist.length ? (vlist[0].created || vlist[0].pubdate || 0) : 0, note: '名称显示已注销' };
    }
    if (!vlist.length) return { mid, uname, status: 'novideo', lastTs: 0 };
    const v = vlist[0];
    return { mid, uname, status: 'ok', lastTs: v.created || v.pubdate || 0, title: v.title || '' };
  }

  async function scanLoop() {
    S.scanning = true; S.stopped = false; S.paused = false;
    render();
    try {
      await loadWbi(true);
      while (!S.stopped) {
        if (S.paused) { await sleep(400); continue; }

        if (!S.queue.length) {
          if (S.totalPages && S.cursorPage > S.totalPages) break;
          const list = await fetchFollowPage(S.cursorPage);
          if (!list.length) break;
          S.totalPages = Math.ceil(S.total / CFG.pageSize);
          S.queue = list.filter((u) => !S.results[u.mid]).map((u) => ({ mid: u.mid, uname: u.uname }));
          S.cursorPage++;
          save();
          setNote(`已取到第 ${S.cursorPage - 1}/${S.totalPages} 页`);
          if (!S.queue.length) continue;
        }

        const item = S.queue.shift();
        if (!item || S.results[item.mid]) continue;

        let rec;
        try {
          rec = await checkUser(item.mid, item.uname);
        } catch (e) {
          if (e instanceof RiskError) {
            S.paused = true;
            setNote('⚠️ 触发风控，已自动暂停：' + e.message + '。建议等待 2 小时后点「继续」。');
            render();
            await sleep(CFG.riskCooldown);
            continue;
          }
          rec = { mid: item.mid, uname: item.uname, status: 'error', lastTs: 0, note: String(e.message || e).slice(0, 80) };
        }

        S.results[item.mid] = rec;
        if (Object.keys(S.results).length % 5 === 0) save();
        render();
        await sleep(rnd(CFG.scanDelayMin, CFG.scanDelayMax));
      }
    } catch (e) {
      setNote('❌ 已停止：' + (e.message || e));
    } finally {
      S.scanning = false;
      save();
      render();
    }
  }

  // ============ 取关 ============
  async function unfollowOne(mid) {
    const csrf = (document.cookie.match(/bili_jct=([^;]+)/) || [])[1];
    if (!csrf) throw new Error('读不到 bili_jct，请确认已登录');
    const body = new URLSearchParams({ fid: String(mid), act: '2', re_src: '11', csrf });
    const j = await fetchJson(BILI + '/x/relation/modify', {
      method: 'POST',
      headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
      body: body.toString(),
    });
    return j;
  }

  async function unfollowLoop() {
    const targets = Object.values(S.results).filter(isTarget);
    if (!targets.length) { alert('没有待取关的账号。'); return; }

    if (S.unfollow.date !== today()) S.unfollow = { date: today(), count: 0 };
    const remain = CFG.dailyUnfollowCap - S.unfollow.count;
    if (remain <= 0) { alert(`今天已达上限 ${CFG.dailyUnfollowCap} 个，明天再来。`); return; }

    const batch = targets.slice(0, remain);
    const ok = confirm(
      `即将取关 ${batch.length} 个账号（今日剩余额度 ${remain}）。\n` +
      `其中：一年未更新 ${batch.filter(isStale).length} 个，已注销 ${batch.filter(isDead).length} 个。\n\n` +
      `取关不可撤销，确认继续？`
    );
    if (!ok) return;

    S.stopped = false; S.paused = false;
    let done = 0, fail = 0;
    for (const t of batch) {
      if (S.stopped) break;
      while (S.paused) await sleep(500);
      try {
        const j = await unfollowOne(t.mid);
        if (j.code === 0) { t.unfollowed = true; done++; bumpUnfollow(); }
        else { fail++; setNote(`取关 ${t.uname} 失败：code=${j.code} ${j.message || ''}`); }
      } catch (e) {
        if (e instanceof RiskError) {
          S.paused = true;
          setNote('⚠️ 取关触发风控，已暂停：' + e.message);
          await sleep(CFG.riskCooldown);
          continue;
        }
        fail++;
      }
      render();
      await sleep(rnd(CFG.unfollowDelayMin, CFG.unfollowDelayMax));
    }
    save();
    alert(`本轮结束：成功 ${done}，失败 ${fail}。`);
  }

  // ============ 导出 ============
  function exportCsv() {
    const rows = [['UP主', 'UID', '空间链接', '最后投稿', '距今天数', '状态', '判定']];
    Object.values(S.results).forEach((r) => {
      rows.push([
        r.uname || '', r.mid,
        'https://space.bilibili.com/' + r.mid,
        fmtDate(r.lastTs),
        daysAgo(r.lastTs) === null ? '' : daysAgo(r.lastTs),
        r.status === 'deleted' ? '已注销' : r.status === 'novideo' ? '无视频投稿' : r.status === 'error' ? '查询异常:' + (r.note || '') : '正常',
        isDead(r) ? '待取关(注销)' : isStale(r) ? '待取关(一年未更)' : '保留',
      ]);
    });
    const csv = '\ufeff' + rows.map((r) => r.map((c) => `"${String(c).replace(/"/g, '""')}"`).join(',')).join('\r\n');
    const blob = new Blob([csv], { type: 'text/csv;charset=utf-8' });
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = 'bili_follow_report_' + today() + '.csv';
    a.click();
    setTimeout(() => URL.revokeObjectURL(a.href), 5000);
  }

  // ============ 进度迁移（换电脑用） ============
  function exportState() {
    const data = {
      v: 1, exportedAt: today(),
      mid: S.mid, total: S.total, totalPages: S.totalPages, cursorPage: S.cursorPage,
      queue: S.queue, results: S.results, unfollow: S.unfollow,
    };
    const blob = new Blob([JSON.stringify(data)], { type: 'application/json' });
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = 'bili_cleanup_state_' + today() + '.json';
    a.click();
    setTimeout(() => URL.revokeObjectURL(a.href), 5000);
  }

  function importState() {
    const inp = document.createElement('input');
    inp.type = 'file';
    inp.accept = '.json,application/json';
    inp.onchange = () => {
      const f = inp.files && inp.files[0];
      if (!f) return;
      const fr = new FileReader();
      fr.onload = () => {
        try {
          const o = JSON.parse(fr.result);
          if (!o || typeof o !== 'object' || !o.results) throw new Error('不是有效的进度文件');
          S.mid = o.mid || S.mid;
          S.total = o.total || S.total;
          S.totalPages = o.totalPages || S.totalPages;
          S.cursorPage = o.cursorPage || 1;
          S.queue = Array.isArray(o.queue) ? o.queue : [];
          S.results = o.results;
          // 同一天换机时把当日额度一并带过来，避免重复超额
          if (o.unfollow && o.unfollow.date === today()) S.unfollow = o.unfollow;
          normalizeResults();
          save(); render();
          alert('导入成功：' + Object.keys(S.results).length + ' 条记录，已完成取关 ' +
            Object.values(S.results).filter((r) => r.unfollowed).length + ' 个');
        } catch (e) {
          alert('导入失败：' + (e.message || e));
        }
      };
      fr.readAsText(f, 'utf-8');
    };
    inp.click();
  }

  // ============ UI ============
  let panel, bodyEl, noteEl, statEl;
  function setNote(t) { S.note = t; if (noteEl) noteEl.textContent = t; }

  function stats() {
    const all = Object.values(S.results);
    return {
      checked: all.length,
      dead: all.filter(isDead).length,
      stale: all.filter(isStale).length,
      novideo: all.filter((r) => r.status === 'novideo').length,
      error: all.filter((r) => r.status === 'error').length,
      done: all.filter((r) => r.unfollowed).length,
    };
  }

  function render() {
    if (!panel) return;
    const st = stats();
    statEl.innerHTML =
      `关注总数 <b>${S.total || '?'}</b> ｜ 已查 <b>${st.checked}</b> ｜ ` +
      `<span style="color:#e6a23c">一年未更 <b>${st.stale}</b></span> ｜ ` +
      `<span style="color:#f56c6c">已注销 <b>${st.dead}</b></span> ｜ ` +
      `无视频 ${st.novideo} ｜ 异常 ${st.error} ｜ 已取关 <b>${st.done}</b>` +
      (S.scanning ? (S.paused ? ' ｜ <span style="color:#e6a23c">已暂停</span>' : ' ｜ <span style="color:#67c23a">扫描中…</span>') : '');

    const list = Object.values(S.results).filter(isTarget)
      .sort((a, b) => (a.lastTs || 0) - (b.lastTs || 0)).slice(0, 200);

    bodyEl.innerHTML = list.length
      ? list.map((r) => `<tr>
          <td style="padding:2px 6px;white-space:nowrap">${escapeHtml(r.uname || '')}</td>
          <td style="padding:2px 6px;color:#888">${r.mid}</td>
          <td style="padding:2px 6px;white-space:nowrap">${fmtDate(r.lastTs)}</td>
          <td style="padding:2px 6px;white-space:nowrap">${daysAgo(r.lastTs) === null ? '—' : daysAgo(r.lastTs) + ' 天'}</td>
          <td style="padding:2px 6px;white-space:nowrap;color:${isDead(r) ? '#f56c6c' : '#e6a23c'}">${isDead(r) ? '已注销' : '一年未更'}</td>
        </tr>`).join('')
      : '<tr><td colspan="5" style="padding:8px;color:#888">暂无待取关账号</td></tr>';
  }

  function escapeHtml(s) {
    return String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
  }

  function buildUI() {
    panel = document.createElement('div');
    panel.style.cssText = 'position:fixed;right:16px;top:80px;width:560px;max-height:70vh;overflow:auto;z-index:999999;' +
      'background:#fff;color:#222;border:1px solid #ddd;border-radius:10px;box-shadow:0 8px 28px rgba(0,0,0,.18);' +
      'font:12px/1.6 -apple-system,"Microsoft YaHei",sans-serif;padding:12px;';

    panel.innerHTML = `
      <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:6px">
        <b style="font-size:13px">B站关注清理助手</b>
        <span style="cursor:pointer;color:#999" data-x>✕</span>
      </div>
      <div data-stat style="background:#f7f8fa;border-radius:6px;padding:6px 8px;margin-bottom:8px"></div>
      <div style="display:flex;gap:6px;flex-wrap:wrap;margin-bottom:8px">
        <button data-act="scan">开始/继续扫描</button>
        <button data-act="pause">暂停</button>
        <button data-act="stop">停止</button>
        <button data-act="csv">导出 CSV</button>
        <button data-act="export">导出进度</button>
        <button data-act="import">导入进度</button>
        <button data-act="retry" style="color:#e6a23c">重试异常项</button>
        <button data-act="unfollow" style="color:#c00">按清单取关</button>
        <button data-act="reset" style="color:#888">清空缓存</button>
      </div>
      <div data-note style="color:#666;margin-bottom:8px">准备就绪。默认只读，不会改动你的关注。</div>
      <table style="width:100%;border-collapse:collapse;font-size:12px">
        <thead><tr style="text-align:left;color:#888">
          <th style="padding:2px 6px">UP主</th><th style="padding:2px 6px">UID</th>
          <th style="padding:2px 6px">最后投稿</th><th style="padding:2px 6px">距今</th><th style="padding:2px 6px">判定</th>
        </tr></thead>
        <tbody data-body></tbody>
      </table>`;

    document.body.appendChild(panel);
    statEl = panel.querySelector('[data-stat]');
    noteEl = panel.querySelector('[data-note]');
    bodyEl = panel.querySelector('[data-body]');

    panel.addEventListener('click', async (ev) => {
      const act = ev.target.getAttribute('data-act');
      if (ev.target.hasAttribute('data-x')) { panel.remove(); panel = null; return; }
      if (!act) return;
      if (act === 'scan') {
        if (S.scanning) { S.paused = false; setNote('继续扫描…'); render(); return; }
        if (!S.mid) {
          const nav = await fetchJson(BILI + '/x/web-interface/nav');
          if (nav.code !== 0 || !nav.data.isLogin) { alert('未登录，请先登录 B 站'); return; }
          S.mid = nav.data.mid;
        }
        if (!S.totalPages && !S.total) { /* 首次 */ }
        scanLoop();
      } else if (act === 'pause') {
        S.paused = true; setNote('已暂停，点「开始/继续扫描」恢复。'); render();
      } else if (act === 'stop') {
        S.stopped = true; setNote('已停止。'); render();
      } else if (act === 'csv') {
        exportCsv();
      } else if (act === 'export') {
        exportState();
      } else if (act === 'import') {
        if (S.scanning) { alert('请先停止扫描再导入。'); return; }
        importState();
      } else if (act === 'retry') {
        let n = 0;
        Object.keys(S.results).forEach((k) => {
          if (S.results[k] && S.results[k].status === 'error') { delete S.results[k]; n++; }
        });
        save(); render();
        setNote(n ? `已清除 ${n} 条异常记录，点「开始/继续扫描」重查。` : '没有异常记录。');
      } else if (act === 'unfollow') {
        if (S.scanning) { alert('请先停止扫描再取关。'); return; }
        unfollowLoop();
      } else if (act === 'reset') {
        if (confirm('清空本地缓存（结果与进度）？已取关的账号不受影响。')) {
          localStorage.removeItem(KEY); location.reload();
        }
      }
    });

    render();
  }

  // ============ 启动 ============
  load();
  normalizeResults();   // 把已缓存结果里的「账号已注销」就地修正为已注销
  if (S.unfollow && S.unfollow.date !== today()) S.unfollow = { date: today(), count: 0 };
  const boot = () => { if (!document.body) return setTimeout(boot, 500); buildUI(); };
  boot();
})();
