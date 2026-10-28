// ==UserScript==
// @name         B站注意力伴侣｜视频分类·评论限时·防沉迷胶囊
// @namespace    local.bilibili.attention-companion
// @version      3.0.0
// @description  本地分层分类、有效浏览统计、评论限时、行为提醒与七日报告
// @match        https://www.bilibili.com/*
// @match        https://search.bilibili.com/*
// @match        https://space.bilibili.com/*
// @match        https://live.bilibili.com/*
// @run-at       document-idle
// @noframes
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_deleteValue
// @grant        GM_listValues
// @grant        GM_addValueChangeListener
// @grant        GM_removeValueChangeListener
// @grant        GM_registerMenuCommand
// @grant        GM_unregisterMenuCommand
// @grant        GM_xmlhttpRequest
// @grant        unsafeWindow
// @connect      api.bilibili.com
// ==/UserScript==

(function () {
  'use strict';
  // ===== 统计核心：独占分片 + 时间区间并集，跨标签不共写累计对象 =====
  const Core = (() => {
    const KEYS = Object.freeze({ epoch: 'bac3-epoch', signal: 'bac3-signal', settings: 'bac3-settings', capacity: 'bac3-capacity' });
    const DEFAULTS = Object.freeze({ commentSoft: 120, commentHard: 180, autoFold: true, sessionLimit: 900,
      dailyLimit: 2700, idleSeconds: 70, useApi: true, topicHint: true, retentionDays: 14, mode: 'normal',
      budgetSeconds: 1800, quickWindowSeconds: 300, quickCount: 8, shortVisitSeconds: 20, shortRatio: 0.6,
      reminderCooldown: 180, commentReturnCount: 3, opacity: 0.94, compact: false, strictMode: false,
      autoCollapseSeconds: 15, commentIdleSeconds: 30, sessionGapSeconds: 600, validSeconds: 6, videoMilestones: [5, 10] });
    const finite = (value, fallback = 0) => Number.isFinite(Number(value)) ? Number(value) : fallback;
    const clamp = (value, min, max, fallback) => Math.min(max, Math.max(min, finite(value, fallback)));
    function normalizeConfig(input = {}) {
      const out = { ...DEFAULTS, ...(input && typeof input === 'object' ? input : {}) };
      const bounds = { commentSoft: [10, 3600], commentHard: [20, 7200], sessionLimit: [60, 28800], dailyLimit: [60, 86400],
        idleSeconds: [10, 600], commentIdleSeconds: [10, 120], budgetSeconds: [0, 28800], quickWindowSeconds: [60, 900], quickCount: [3, 40],
        shortVisitSeconds: [3, 120], shortRatio: [0.3, 1], reminderCooldown: [30, 3600], commentReturnCount: [2, 20],
        opacity: [0.35, 1], autoCollapseSeconds: [0, 120], sessionGapSeconds: [60, 3600], validSeconds: [6, 60] };
      for (const [key, [min, max]] of Object.entries(bounds)) out[key] = clamp(out[key], min, max, DEFAULTS[key]);
      out.commentHard = Math.max(out.commentSoft + 10, out.commentHard);
      for (const key of ['autoFold', 'useApi', 'topicHint', 'compact', 'strictMode']) out[key] = !!out[key];
      out.retentionDays = Number(out.retentionDays) === 30 ? 30 : 14;
      out.mode = ['normal', 'learning', 'entertainment'].includes(out.mode) ? out.mode : 'normal';
      out.aliases = Object.fromEntries(Object.entries(out.aliases || {}).filter(([key, value]) => typeof key === 'string' && typeof value === 'string' && key.length <= 64 && value.length <= 64).slice(-1000));
      out.videoMilestones = Array.isArray(out.videoMilestones) ? out.videoMilestones.filter(n => Number.isInteger(n) && n > 0).slice(0, 10) : [5, 10];
      return out;
    }
    function dayKey(ms = Date.now()) {
      const d = new Date(ms);
      return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`;
    }
    function dayStart(ms) { const d = new Date(ms); d.setHours(0, 0, 0, 0); return d.getTime(); }
    function previousDay(ms, n = 1) { const d = new Date(ms); d.setDate(d.getDate() - n); return d.getTime(); }
    function splitInterval(start, end) {
      const pieces = [];
      if (!Number.isFinite(start) || !Number.isFinite(end) || end <= start) return pieces;
      let cursor = start;
      while (cursor < end && pieces.length < 32) {
        const d = new Date(cursor); d.setHours(24, 0, 0, 0);
        const next = Math.min(end, d.getTime());
        pieces.push({ date: dayKey(cursor), start: cursor, end: next }); cursor = next;
      }
      return pieces;
    }
    function mergedIntervals(intervals) {
      const sorted = intervals.filter(x => Number.isFinite(x.start) && Number.isFinite(x.end) && x.end > x.start)
        .map(x => ({ start: x.start, end: x.end })).sort((a, b) => a.start - b.start || a.end - b.end);
      const result = [];
      for (const item of sorted) {
        const last = result[result.length - 1];
        if (last && item.start <= last.end) last.end = Math.max(last.end, item.end);
        else result.push(item);
      }
      return result;
    }
    function unionDuration(intervals) { return mergedIntervals(intervals).reduce((sum, x) => sum + (x.end - x.start) / 1000, 0); }
    function intersectionDuration(a, b) {
      const aa = mergedIntervals(a), bb = mergedIntervals(b); let i = 0, j = 0, total = 0;
      while (i < aa.length && j < bb.length) {
        total += Math.max(0, Math.min(aa[i].end, bb[j].end) - Math.max(aa[i].start, bb[j].start));
        if (aa[i].end < bb[j].end) i++; else j++;
      }
      return total / 1000;
    }
    function canonicalId(value, aliases = {}) {
      let id = String(value || '');
      const seen = new Set();
      for (let i = 0; i < 8 && !seen.has(id); i++) {
        seen.add(id); const next = aliases[id] || aliases[id.toLowerCase()];
        if (!next || typeof next !== 'string') break;
        id = next;
      }
      return id;
    }
    function aggregate(shards, date = dayKey(), now = Date.now(), overrides = {}, config = DEFAULTS) {
      const cfg = normalizeConfig(config);
      const result = { date, siteSeconds: 0, backgroundSeconds: 0, idleSeconds: 0, commentSeconds: 0,
        categorySeconds: {}, validVideos: {}, videoCount: 0, openCount: 0, opens: 0, commentEntries: 0,
        quickSwitches: 0, bingeEpisodes: 0, reminders: 0, exitEstimates: 0, sessionSeconds: 0,
        sessionId: '', sessionStartedAt: 0, error: '',
        interventions: { fold: 0, leaveVideo: 0, stopSwitch: 0, exit: 0, return: 0 }, events: [], limited: false, imported: false };
      const videoKey = video => canonicalId(video, cfg.aliases);
      const categoryFor = (video, fallback) => overrides[videoKey(video)]?.category || overrides[video]?.category || fallback || '其他／未知';
      const points = [], comments = [], active = [], sessionActive = [], events = new Map();
      let itemId = 0, latestSessionReset = 0;
      for (const shard of shards || []) {
        if (!shard || !Array.isArray(shard.intervals)) continue;
        result.limited ||= !!shard.limited;
        for (const event of (shard.events || [])) {
          if (!event || !event.id || !Number.isFinite(event.at)) continue;
          if (event.type === 'sessionReset') latestSessionReset = Math.max(latestSessionReset, event.at);
          if (dayKey(event.at) === date) events.set(event.id, event);
        }
        for (const raw of shard.intervals) {
          if (!raw || !Number.isFinite(raw.start) || !Number.isFinite(raw.end) || raw.end <= raw.start) continue;
          const item = { ...raw, end: Math.min(raw.end, now), uid: `${shard.id || ''}:${itemId++}` };
          if (item.end <= item.start) continue;
          if (item.kind === 'active') sessionActive.push(item);
          if (shard.date !== date) continue;
          if (item.kind === 'comment') { comments.push(item); continue; }
          if (!['active', 'background', 'idle'].includes(item.kind)) continue;
          if (item.kind === 'active') active.push(item);
          points.push({ at: item.start, add: true, item }, { at: item.end, add: false, item });
        }
        if (shard.date === date && shard.legacy) {
          const legacy = shard.legacy; result.imported = true;
          result.siteSeconds += Math.max(0, finite(legacy.siteSeconds)); result.commentSeconds += Math.max(0, finite(legacy.commentSeconds));
          for (const [video, category] of Object.entries(legacy.videos || {})) result.validVideos[videoKey(video)] = categoryFor(video, category);
          for (const [category, seconds] of Object.entries(legacy.categorySeconds || {})) result.categorySeconds[category] = (result.categorySeconds[category] || 0) + Math.max(0, finite(seconds));
        }
      }
      // 同一时刻只选一个计时归属。焦点时间较新的前台窗口优先，UUID 用于稳定打破平局。
      const priority = { active: 3, background: 2, idle: 1 }, live = new Map();
      const winner = () => {
        let best;
        for (const item of live.values()) if (!best || priority[item.kind] > priority[best.kind] ||
          (priority[item.kind] === priority[best.kind] && (finite(item.focusAt) > finite(best.focusAt) ||
          (finite(item.focusAt) === finite(best.focusAt) && item.uid > best.uid)))) best = item;
        return best;
      };
      points.sort((a, b) => a.at - b.at || Number(a.add) - Number(b.add));
      let previous = points[0]?.at;
      for (let i = 0; i < points.length;) {
        const at = points[i].at, owner = winner(), seconds = (at - previous) / 1000;
        if (owner && seconds > 0) {
          if (owner.kind === 'active') {
            result.siteSeconds += seconds;
            if (owner.video) {
              const category = categoryFor(owner.video, owner.category);
              result.categorySeconds[category] = (result.categorySeconds[category] || 0) + seconds;
            }
          } else if (owner.kind === 'background') result.backgroundSeconds += seconds;
          else result.idleSeconds += seconds;
        }
        while (i < points.length && points[i].at === at) { const point = points[i++]; if (point.add) live.set(point.item.uid, point.item); else live.delete(point.item.uid); }
        previous = at;
      }
      result.commentSeconds += intersectionDuration(comments, active);
      result.events = [...events.values()].sort((a, b) => a.at - b.at || a.id.localeCompare(b.id));
      for (const event of result.events) {
        const payload = event.payload || {};
        if (event.type === 'open') result.openCount++;
        if (event.type === 'valid' && (payload.video || payload.videoId)) {
          const video = payload.video || payload.videoId;
          result.validVideos[videoKey(video)] = categoryFor(video, payload.category);
        }
        if (event.type === 'commentEnter') result.commentEntries++;
        if (event.type === 'quickSwitch') result.quickSwitches++;
        if (event.type === 'binge') result.bingeEpisodes++;
        if (event.type === 'reminder') result.reminders++;
        if (event.type === 'intervention' && Object.hasOwn(result.interventions, payload.action)) result.interventions[payload.action]++;
      }
      result.exitEstimates = result.interventions.exit; result.opens = result.openCount;
      result.videoCount = Object.keys(result.validVideos).length;
      const merged = mergedIntervals(sessionActive.map(x => ({ start: Math.max(x.start, latestSessionReset), end: x.end })));
      let session = 0, lastEnd = 0, sessionStartedAt = 0;
      for (const x of merged) {
        if (!lastEnd || x.start - lastEnd > cfg.sessionGapSeconds * 1000) { session = 0; sessionStartedAt = x.start; }
        session += (x.end - x.start) / 1000; lastEnd = x.end;
      }
      const sessionCurrent = lastEnd && now - lastEnd <= cfg.sessionGapSeconds * 1000;
      result.sessionSeconds = sessionCurrent ? session : 0;
      result.sessionStartedAt = sessionCurrent ? sessionStartedAt : 0;
      result.sessionId = sessionCurrent ? `${latestSessionReset}:${sessionStartedAt}` : '';
      return result;
    }
    function detectBehavior(visits, config = DEFAULTS, now = Date.now()) {
      const cfg = normalizeConfig(config), within = seconds => (visits || []).filter(v => finite(v.at ?? v.start) >= now - seconds * 1000 && finite(v.at ?? v.start) <= now);
      const recent = within(cfg.quickWindowSeconds), quarter = within(900);
      const duration = v => finite(v.effectiveSeconds ?? v.seconds ?? v.duration);
      const completed = recent.filter(v => v.end != null || v.closed || v.complete);
      const short = completed.filter(v => duration(v) < cfg.shortVisitSeconds);
      const search = recent.filter(v => v.source === 'search').length;
      const learning = recent.filter(v => v.expression === '教程／教学' || v.expression === '教程/教学' || v.course || v.source === 'course').length;
      const repeat = recent.length - new Set(recent.map(v => canonicalId(v.video || v.videoId || v.id, cfg.aliases)).filter(Boolean)).size;
      const recommendation = recent.filter(v => v.source === 'recommendation').length;
      const enough = recent.length >= cfg.quickCount && completed.length >= Math.max(2, cfg.quickCount - 2);
      const shortRatio = completed.length ? short.length / completed.length : 0;
      const intentional = search >= recent.length / 2 || learning >= recent.length / 2;
      const suspected = enough && shortRatio >= cfg.shortRatio;
      return { count5m: within(300).length, count15m: quarter.length, count: recent.length, shortCount: short.length, shortRatio,
        repeatCount: Math.max(0, repeat), recommendationCount: recommendation, intentional,
        level: suspected ? (intentional ? 1 : 2) : 0,
        reasons: suspected ? [`最近${Math.round(cfg.quickWindowSeconds / 60)}分钟进入${recent.length}个视频`, `${short.length}次有效停留少于${cfg.shortVisitSeconds}秒`, ...(repeat > 1 ? [`重复进入${repeat}次`] : [])] : [],
        message: suspected ? (intentional ? '刚才切换较快。你是在搜索内容或连续学习吗？' : '你刚才连续切换了多个视频。是在找特定内容，还是跟着推荐继续看？') : '' };
    }
    class Store {
      constructor(env = {}) {
        this.env = env; this.now = env.now || Date.now; this.id = env.id || `${this.now().toString(36)}-${Math.random().toString(36).slice(2)}`;
        this.get = env.get || ((key, fallback) => GM_getValue(key, fallback));
        this.set = env.set || ((key, value) => GM_setValue(key, value)); this.list = env.list || (() => GM_listValues()); this.del = env.del || (key => GM_deleteValue(key));
        this.error = ''; this.epoch = this.safeGet(KEYS.epoch, 'initial'); this.shards = new Map(); this.tails = new Map(); this.sequence = 0; this.cache = null; this.capWarning = false;
      }
      safeGet(key, fallback) { try { return this.get(key, fallback); } catch (e) { this.error = `读取失败：${e.message || e}`; return fallback; } }
      safeSet(key, value) { try { this.set(key, value); return true; } catch (e) { this.error = `保存失败：${e.message || e}`; return false; } }
      sync() {
        const epoch = this.safeGet(KEYS.epoch, 'initial');
        if (epoch !== this.epoch) { this.epoch = epoch; this.shards.clear(); this.tails.clear(); this.cache = null; this.capWarning = false; if (this.env.onReset) this.env.onReset(); return true; }
        this.cache = null; return false;
      }
      key(date) { return `bac3-shard:${this.epoch}:${date}:${this.id}`; }
      local(date) {
        if (!this.shards.has(date)) this.shards.set(date, { id: this.id, epoch: this.epoch, date, intervals: [], events: [], updated: this.now(), revision: 0 });
        return this.shards.get(date);
      }
      recordInterval(start, end, kind, category = '其他／未知', video = '', focusAt = 0) {
        this.syncEpoch();
        for (const piece of splitInterval(start, end)) {
          const shard = this.local(piece.date), tailKey = `${piece.date}:${kind}`, last = this.tails.get(tailKey);
          if (last && last.end === piece.start && last.kind === kind && last.category === category && last.video === video && last.focusAt === focusAt) last.end = piece.end;
          else if (shard.intervals.length < 20000) { const interval = { start: piece.start, end: piece.end, kind, category, video, focusAt }; shard.intervals.push(interval); this.tails.set(tailKey, interval); }
          else this.markLimited(shard);
          shard.updated = this.now(); shard.revision++; this.cache = null;
        }
      }
      syncEpoch() { if (this.safeGet(KEYS.epoch, 'initial') !== this.epoch) this.sync(); }
      markLimited(shard) { shard.limited = true; this.capWarning = true; this.safeSet(KEYS.capacity, { at: this.now(), epoch: this.epoch, message: '达到本地容量保护上限，部分记录未保存；请导出或清理统计。' }); }
      event(type, payload = {}, at = this.now()) {
        this.syncEpoch(); const shard = this.local(dayKey(at));
        const event = { id: `${this.id}:${++this.sequence}`, type, payload: { ...payload }, at };
        if (shard.events.length < 12000) shard.events.push(event); else this.markLimited(shard);
        shard.updated = this.now(); shard.revision++; this.cache = null; return event;
      }
      flush() {
        this.syncEpoch(); let ok = true;
        for (const shard of this.shards.values()) {
          // 其他标签清理后，旧代分片只能被遗留，绝不会被汇总进新一代。
          if (this.safeGet(KEYS.epoch, 'initial') !== this.epoch) { this.sync(); return false; }
          if (shard.savedRevision === shard.revision) continue;
          const snapshot = { ...shard, savedRevision: shard.revision };
          if (this.safeSet(this.key(shard.date), snapshot)) shard.savedRevision = shard.revision; else ok = false;
        }
        this.safeSet(KEYS.signal, { at: this.now(), id: this.id, sequence: this.sequence, epoch: this.epoch }); return ok;
      }
      rawShards(date) {
        this.syncEpoch(); const all = new Map(); let keys = [];
        try { keys = this.list(); } catch (e) { this.error = `枚举失败：${e.message || e}`; }
        const prefix = `bac3-shard:${this.epoch}:`;
        for (const key of keys) if (key.startsWith(prefix)) {
          const shard = this.safeGet(key, null);
          if (shard?.epoch === this.epoch && (!date || shard.date === date)) all.set(key, shard);
        }
        for (const [localDate, shard] of this.shards) if (!date || localDate === date) all.set(this.key(localDate), shard);
        return [...all.values()];
      }
      read(date = dayKey(this.now()), now = this.now(), overrides = {}, config = DEFAULTS) {
        const raw = this.rawShards();
        const result = aggregate(raw, date, now, overrides, normalizeConfig(config));
        result.limited ||= this.safeGet(KEYS.capacity, null)?.epoch === this.epoch; result.error = this.error; return result;
      }
      days(n = 7, overrides = {}, config = DEFAULTS) {
        const now = this.now(), raw = this.rawShards();
        return Array.from({ length: n }, (_, i) => aggregate(raw, dayKey(previousDay(now, n - i - 1)), now, overrides, normalizeConfig(config)));
      }
      clear() {
        const next = `${this.now().toString(36)}-${this.id}-${++this.sequence}`;
        if (!this.safeSet(KEYS.epoch, next)) return false;
        this.sync(); this.cleanup(14); this.safeSet(KEYS.signal, { at: this.now(), id: this.id, epoch: next }); return true;
      }
      cleanup(retention = 14) {
        this.syncEpoch();
        const cutoff = dayKey(previousDay(this.now(), retention - 1)); let keys = [];
        try { keys = this.list(); } catch (_) { return; }
        const survivors = [];
        for (const key of keys) if (key.startsWith('bac3-shard:')) {
          const shard = this.safeGet(key, null);
          if (!shard || shard.epoch !== this.epoch || shard.date < cutoff) { try { this.del(key); } catch (_) {} }
          else survivors.push({ key, date: shard.date, updated: shard.updated || 0, bytes: JSON.stringify(shard).length * 2 });
        }
        // 保护浏览器资源：最多 3000 个分片、约 16 MiB UTF-16。超限会显示显式警告。
        survivors.sort((a, b) => a.date.localeCompare(b.date) || a.updated - b.updated);
        let bytes = survivors.reduce((sum, item) => sum + item.bytes, 0);
        while (survivors.length > 3000 || bytes > 16 * 1024 * 1024) {
          const victim = survivors.shift(); if (!victim) break;
          const own = [...this.shards.keys()].some(date => this.key(date) === victim.key);
          if (own) { const shard = this.shards.get(victim.date); if (shard) this.markLimited(shard); break; }
          try { this.del(victim.key); bytes -= victim.bytes; this.markLimited(this.local(dayKey(this.now()))); } catch (_) { break; }
        }
        for (const date of this.shards.keys()) if (date < cutoff) { this.shards.delete(date); for (const key of this.tails.keys()) if (key.startsWith(`${date}:`)) this.tails.delete(key); }
        this.cache = null;
      }
      migrateLegacy() {
        if (this.safeGet(KEYS.settings, null) == null) {
          const old = this.safeGet('bac2-settings', null); if (old && typeof old === 'object') this.safeSet(KEYS.settings, normalizeConfig(old));
        }
        // 固定键 + 只在初始代导入，避免多页迁移翻倍以及“清除后重新导入”。不伪造旧版时间区间。
        if (this.epoch !== 'initial') return;
        const old = this.safeGet('bac2-data', null);
        if (!old || old.date !== dayKey(this.now())) return;
        const key = `bac3-shard:initial:${old.date}:legacy-v2`;
        if (this.safeGet(key, null)) return;
        this.safeSet(key, { id: 'legacy-v2', epoch: 'initial', date: old.date, intervals: [], events: [], updated: this.now(),
          legacy: { siteSeconds: finite(old.siteSeconds), commentSeconds: finite(old.commentSeconds), videos: old.videos || {}, categorySeconds: old.categorySeconds || {} } });
      }
    }
    return { KEYS, DEFAULTS, normalizeConfig, dayKey, dayStart, previousDay, splitInterval, mergedIntervals, unionDuration, intersectionDuration, canonicalId, aggregate, detectBehavior, Store };
  })();
  // ===== 分层分类：规则只是可复核的信号，不判断立场或内容真伪 =====
  const Content = (() => {
    const categories = ['时事与社会', '历史与人文', '财经与商业', '科技与 AI', '学习与知识', '影视与娱乐', '游戏与动漫', '运动与健身', '生活与日常', '其他／未知'];
    const expressions = ['教程／教学', '资料讲解／科普', '纪录／报道', '观点评论', '热点讨论', '娱乐消遣', '无法判断'];
    const rules = [
      [/时政|政治|政策|社会新闻|时事|国际局势|国际关系|地缘|外交|选举|民调|公共议题|中美关系|台海|俄乌|政府|官场|政论/, /社科|社会|资讯|热点|时政/],
      [/历史|人文|史学|朝代|古代|民国|近代史|世界史|中国史|文革|冷战|二战|改革开放|百家争鸣|秦汉|唐宋|明朝|清朝|帝国|苏联|革命史|考古|文物/, /历史|人文|考古/],
      [/财经|经济|投资|商业|金融|股市|股票|基金|理财|产业|就业|房地产|房价|失业|通胀|宏观经济|消费降级|\bETF\b|纳斯达克|标普/i, /财经|金融|商业/],
      [/科技|人工智能|\bAI\b|大模型|ChatGPT|Claude|Gemini|编程|程序员|代码|数码|计算机|软件|互联网|芯片|手机评测|电脑|机器人|Python|JavaScript|机器学习/i, /计算机|软件|科技|数码|人工智能|极客|技术宅/],
      [/科普|读书|哲学|心理学|物理|化学|数学|语言学习|英语|知识/, /科普|知识|校园|职业职场|科学|学习|教育/],
      [/影视|电影|电视剧|影评|综艺|音乐|娱乐|明星|导演|演员|演唱会|追剧|乐器|歌曲|翻唱/, /影视|音乐|娱乐|电影|电视剧|综艺/],
      [/游戏|动漫|动画|电竞|原神|英雄联盟|\bLOL\b|提莫|金铲铲|云顶之弈|王者荣耀|\bCS2\b|\bDOTA\b|二次元|游戏实况/i, /游戏|动画|番剧|国创|鬼畜|电竞/],
      [/运动|健身|肌肉|力量训练|体育|足球|篮球|卧推|深蹲|增肌|跑步|徒步|羽毛球/, /运动|健身|体育|竞技体育/],
      [/日常|vlog|美食|旅行|旅游|摄影|街拍|探店|穿搭|家居|宠物|猫咪|城市漫游|烹饪|做饭/i, /生活|美食|动物|旅行|时尚|家居|汽车/]
    ];
    const expressionRules = [
      /教程|教学|课程|入门|第[一二三四五六七八九十\d]+[课讲]|从零开始|手把手|学习路线/,
      /科普|资料解读|原理|讲解|考据|文献|史料|知识点|解析|揭秘原理/,
      /纪录片|纪录|实录|现场报道|采访|新闻报道|纪实/,
      /我认为|我觉得|如何评价|怎么看|观点|评论|漫谈|看法|锐评|评价|解读|评析/,
      /热议|热点|最新进展|突发|回应|热搜|事件进展/,
      /搞笑|整活|娱乐|游戏实况|演唱|翻唱|音乐现场|混剪|鬼畜|高能集锦/
    ];
    const signalRules = [
      ['公共议题：可进一步核查资料来源', /政治|时政|政策|政府|选举|外交|中美|台海|俄乌|意识形态|民族主义|资本主义|社会主义|文革|历史评价|官方通报|领土|战争|冲突|民主|阶级/],
      ['标题存在情绪化措辞', /震惊|惊天|狠狠|破防|崩溃|逆天|炸裂|细思极恐|笑死|洗脑|觉醒|被封杀/],
      ['标题存在绝对化表达', /绝对|必然|毫无疑问|所有人都|全都是|一切都是|永远|彻底证明|唯一真相|百分之百|100%/],
      ['标题存在贬损或对立措辞', /脑残|无脑|无知|没救了|打脸|带节奏|蠢货|跪舔|谁还敢|不服来辩/]
    ];
    const clean = (v, max = 180) => String(v || '').replace(/\s+/g, ' ').trim().slice(0, max);
    function getVideoIdentity(url) {
      try {
        const u = new URL(url, 'https://www.bilibili.com');
        const m = u.pathname.match(/\/video\/(BV[0-9a-z]{10}|av\d+)(?:\/|$)/i);
        if (!m) return { id: '', key: '', part: 1 };
        const id = /^av/i.test(m[1]) ? m[1].toLowerCase() : 'BV' + m[1].slice(2);
        const part = Math.min(10000, Math.max(1, Math.floor(Number(u.searchParams.get('p')) || 1)));
        return { id, part, key: `${id}:p${part}` };
      } catch (_) { return { id: '', key: '', part: 1 }; }
    }
    function classify(meta = {}, correction) {
      const title = clean(meta.title);
      const area = clean(meta.area);
      const tags = clean(Array.isArray(meta.tags) ? meta.tags.join(' ') : meta.tags, 500);
      const scored = rules.map(([rx, zone], index) => {
        const evidence = [];
        let score = 0;
        if (rx.test(title)) { score += 3; evidence.push(`标题：${title.match(rx)?.[0]}`); }
        if (rx.test(tags)) { score += 3; evidence.push(`标签：${tags.match(rx)?.[0]}`); }
        if (zone.test(area)) { score += index === 4 && /^(知识|学习|教育|科普)$/.test(area) ? 2 : 6; evidence.push(`分区：${area}`); }
        return { index, score, evidence };
      }).sort((a, b) => b.score - a.score);
      const best = scored[0];
      const ambiguous = best.score > 0 && best.score === scored[1].score;
      let category = best.score && !ambiguous ? categories[best.index] : categories[9];
      let confidence = best.score >= 6 && !ambiguous ? '高' : best.score >= 3 && !ambiguous ? '中' : '低';
      let evidence = best.score && !ambiguous ? best.evidence : [ambiguous ? '多个主题证据相近，暂不确定' : '标题、分区和标签不足以识别主题'];
      let expression = '无法判断';
      // 标题优先；表达类型不能仅由主题类别推测。
      const titleMatches = expressionRules.map((rx, i) => rx.test(title) ? i : -1).filter(i => i >= 0);
      const extraMatches = expressionRules.map((rx, i) => rx.test(`${area} ${tags}`) ? i : -1).filter(i => i >= 0);
      const matches = titleMatches.length ? titleMatches : extraMatches;
      if (matches.length) {
        // 教程/纪录等形式证据优先于宽泛的“解读”。
        const index = matches.includes(0) ? 0 : matches.includes(2) ? 2 : matches.length === 1 ? matches[0] : -1;
        if (index >= 0) {
          expression = expressions[index];
          const source = titleMatches.length ? title : `${area} ${tags}`;
          evidence.push(`表达依据：${source.match(expressionRules[index])?.[0] || '结构化信息'}`);
        }
      }
      const signals = signalRules.filter(([, rx], i) => rx.test(i === 0 ? `${title} ${area} ${tags}` : title)).map(([label]) => label);
      if (expression === '观点评论' && category === '历史与人文' && /评价|人物|功过|争议/.test(title)) {
        if (!signals.includes(signalRules[0][0])) signals.push(signalRules[0][0]);
      }
      if (correction && typeof correction === 'object') {
        let applied = false;
        if (categories.includes(correction.category)) { category = correction.category; applied = true; }
        if (expressions.includes(correction.expression)) { expression = correction.expression; applied = true; }
        if (applied) { confidence = '高'; evidence = ['用户手动修正（本地保存）', ...evidence]; }
      }
      return { category, expression, confidence, evidence, signals, title, source: clean(meta.source || '本地规则'), topic: signals.includes(signalRules[0][0]), emotional: signals.some(x => /情绪化|绝对化|贬损/.test(x)) };
    }
    function readMetadata(doc, pageWindow, id, options = {}) {
      const meta = { title: '', area: '', tags: '', source: '页面信息（本地规则）' };
      const state = (() => { try { return pageWindow?.__INITIAL_STATE__; } catch (_) { return null; } })();
      const vd = state?.videoData;
      const same = vd && (String(vd.bvid || '') === id || `av${vd.aid}` === id.toLowerCase());
      if (same) {
        meta.title = clean(vd.title); meta.area = clean(vd.tname || vd.tname_v2);
        meta.bvid = clean(vd.bvid, 20); meta.aid = vd.aid; meta.source = '页面视频信息';
        if (Array.isArray(state.tags)) meta.tags = state.tags.map(t => clean(t.tag_name, 40)).filter(Boolean).slice(0, 16).join(' ');
      }
      // 路由刚切换时保留空标题；标题与标签均可能比 URL 晚一个渲染周期更新。
      if (options.allowTitle !== false) {
        const normalizeTitle = value => clean(value).replace(/_哔哩哔哩.*| - 哔哩哔哩.*/gi, '').trim();
        const el = doc.querySelector('h1.video-title, h1[title], #viewbox_report h1');
        const heading = normalizeTitle(el?.getAttribute('title') || el?.textContent);
        const documentTitle = normalizeTitle(doc.title);
        const ogTitle = normalizeTitle(doc.querySelector('meta[property="og:title"]')?.content);
        const previous = normalizeTitle(options.previousTitle);
        const eligible = value => value && (!previous || value !== previous);
        if (!meta.title) meta.title = [heading, documentTitle, ogTitle].find(eligible) || '';
        // 只有当前 h1 已更新或结构化信息身份匹配，才采用可能残留的 DOM 标签。
        const tagsCurrent = same || !previous || !!eligible(heading);
        if (!meta.tags && tagsCurrent) meta.tags = [...doc.querySelectorAll('.video-tag-container .tag-link, .tag-area a, .tag-container a')].slice(0, 16).map(x => clean(x.textContent, 40)).filter(Boolean).join(' ');
      }
      return meta;
    }
    const CACHE = 'bac3-meta:';
    const ALIAS = 'bac3-alias:';
    const FIX = 'bac3-correction:';
    const sameID = id => /^(BV[0-9A-Za-z]{10}|av\d+)$/.test(id);
    const fallbacks = new WeakMap();
    function safeEnvironment(env) {
      if (env.__contentSafe) return env;
      let fallbackState = fallbacks.get(env);
      if (!fallbackState) { fallbackState = { memory: new Map(), dirty: new Set() }; fallbacks.set(env, fallbackState); }
      const { memory, dirty } = fallbackState;
      const report = error => { try { env.onError?.(error); } catch (_) {} };
      return { ...env, __contentSafe: true,
        get(key, fallback) { if (dirty.has(key)) return memory.has(key) ? memory.get(key) : fallback; try { return env.get(key, fallback); } catch (e) { report(e); return memory.has(key) ? memory.get(key) : fallback; } },
        set(key, value) { memory.set(key, value); try { const result = env.set(key, value); dirty.delete(key); return result; } catch (e) { dirty.add(key); report(e); } },
        del(key) { memory.delete(key); try { const result = env.del(key); dirty.delete(key); return result; } catch (e) { dirty.add(key); report(e); } },
        list() { try { return [...new Set([...(env.list?.() || []), ...memory.keys()])]; } catch (e) { report(e); return [...memory.keys()]; } }
      };
    }
    function canonical(env, id) { env = safeEnvironment(env); return env.get(ALIAS + id, id) || id; }
    function cleanupCorrections(env) {
      env = safeEnvironment(env);
      // 修正没有时间到期；超过500条时按最近保存时间保留，避免静默无限增长。
      const saved = env.list().filter(k => k.startsWith(FIX)).map(k => ({ k, at: Number(env.get(k, null)?.at) || 0 })).sort((a, b) => b.at - a.at || a.k.localeCompare(b.k));
      for (let i = 500; i < saved.length; i++) env.del(saved[i].k);
    }
    function getCorrection(env, id) { env = safeEnvironment(env); return env.get(FIX + canonical(env, id), null); }
    function setCorrection(env, id, value) {
      env = safeEnvironment(env);
      const key = FIX + canonical(env, id);
      if (!value) { env.del(key); return; }
      env.set(key, { category: categories.includes(value.category) ? value.category : undefined, expression: expressions.includes(value.expression) ? value.expression : undefined, at: (env.now || Date.now)() });
      cleanupCorrections(env);
    }
    function createLoader(env) {
      env = safeEnvironment(env);
      const now = env.now || Date.now;
      const pending = new Map();
      const queue = [];
      const owner = Math.random().toString(36).slice(2);
      let timer, active = false, lastRequest = -Infinity, destroyed = false;
      function cleanup() {
        cleanupCorrections(env);
        const all = env.list().filter(k => k.startsWith(CACHE)).map(k => ({ k, v: env.get(k, null) })).filter(x => x.v);
        all.sort((a, b) => (b.v.at || 0) - (a.v.at || 0));
        for (let i = 0; i < all.length; i++) if (i >= 300 || now() - (all[i].v.at || 0) > 7 * 86400000) env.del(all[i].k);
        for (const k of env.list().filter(k => k.startsWith('bac3-request:'))) if (now() - (env.get(k, 0) || 0) > 60000) env.del(k);
        for (const k of env.list().filter(k => k.startsWith(ALIAS))) {
          const target = env.get(k, '');
          if (!env.get(CACHE + target, null) && !env.get(FIX + target, null)) env.del(k);
        }
      }
      function pump() {
        clearTimeout(timer);
        if (active || destroyed) return;
        while (queue.length && !pending.has(queue[0])) queue.shift();
        if (!queue.length) return;
        const recent = env.list().filter(k => k.startsWith('bac3-request:')).map(k => Number(env.get(k, 0)) || 0);
        const lastGlobal = recent.length ? Math.max(...recent) : -Infinity;
        const wait = Math.max(lastRequest + 5000 - now(), lastGlobal + 5000 - now(), 0);
        if (wait) { timer = setTimeout(pump, Math.min(wait, 5000)); return; }
        const id = queue.shift();
        const item = pending.get(id);
        if (!item) { pump(); return; }
        active = true; lastRequest = now();
        // 各实例只写自己的请求时间；此处是跨标签建议限频，GM 存储不提供原子锁。
        env.set(`bac3-request:${owner}`, lastRequest);
        let done = false;
        const finish = (meta, error) => {
          if (done) return; done = true; active = false;
          pending.delete(id);
          if (!destroyed) {
            if (!meta) env.set(CACHE + id, { at: now(), failed: true });
            for (const cb of item.callbacks) { try { cb(meta, error); } catch (e) { env.onError?.(e); } }
          }
          pump();
        };
        try {
          item.handle = env.request({
            method: 'GET', anonymous: true,
            url: `https://api.bilibili.com/x/web-interface/view?${id.startsWith('BV') ? 'bvid=' : 'aid='}${encodeURIComponent(id.startsWith('BV') ? id : id.slice(2))}`,
            timeout: 6500,
            onload(response) {
              if (destroyed) return;
              try {
                const json = JSON.parse(response.responseText);
                const vd = json.data;
                const matches = vd && (vd.bvid === id || `av${vd.aid}` === id);
                if (response.status && response.status !== 200 || json.code !== 0 || !matches) throw new Error('视频信息接口不可用');
                const meta = { title: clean(vd.title), area: clean(vd.tname || vd.tname_v2), bvid: clean(vd.bvid, 20), aid: vd.aid, source: 'B站视频信息接口' };
                env.set(CACHE + id, { at: now(), meta });
                if (sameID(meta.bvid)) {
                  env.set(CACHE + meta.bvid, { at: now(), meta });
                  env.set(ALIAS + `av${vd.aid}`, meta.bvid);
                  const oldFix = env.get(FIX + `av${vd.aid}`, null), newFix = env.get(FIX + meta.bvid, null);
                  if (oldFix) {
                    if (!newFix || (oldFix.at || 0) > (newFix.at || 0)) env.set(FIX + meta.bvid, oldFix);
                    env.del(FIX + `av${vd.aid}`);
                  }
                }
                finish(meta);
              } catch (e) { finish(null, e); }
            },
            onerror: () => finish(null, new Error('视频信息请求失败')),
            ontimeout: () => finish(null, new Error('视频信息请求超时')),
            onabort: () => finish(null, new Error('视频信息请求已取消'))
          });
        } catch (e) { finish(null, e); }
      }
      function load(id, callback) {
        if (!sameID(id) || destroyed) return () => {};
        id = canonical(env, id);
        const cached = env.get(CACHE + id, null);
        if (cached && now() - cached.at < (cached.failed ? 600000 : 7 * 86400000)) { callback(cached.meta || null, cached.failed ? new Error('请求失败，退避中') : undefined); return () => {}; }
        if (!pending.has(id)) { pending.set(id, { callbacks: new Set() }); queue.push(id); }
        const item = pending.get(id);
        item.callbacks.add(callback);
        pump();
        return () => { item.callbacks.delete(callback); if (!item.callbacks.size && !item.handle) pending.delete(id); };
      }
      return { load, cleanup, destroy() { destroyed = true; clearTimeout(timer); for (const item of pending.values()) { try { item.handle?.abort?.(); } catch (_) {} } pending.clear(); env.del(`bac3-request:${owner}`); } };
    }
    return { categories, expressions, classify, getVideoIdentity, readMetadata, createLoader, canonical, getCorrection, setCorrection };
  })();
  // ===== 页面适配、状态机与统一提醒中心 =====
  function createApp() {
    const env = {
      get: (key, fallback) => GM_getValue(key, fallback),
      set: (key, value) => GM_setValue(key, value),
      list: () => GM_listValues(), del: key => GM_deleteValue(key),
      now: () => Date.now()
    };
    const safeGet = (k, d) => { try { return env.get(k, d); } catch (_) { return d; } };
    let cfg = Core.normalizeConfig({...safeGet('bac2-settings', {}), ...safeGet('bac3-settings', {})});
    const now = () => Date.now();
    const uid = () => globalThis.crypto?.randomUUID?.() || `${now()}-${Math.random().toString(36).slice(2)}`;
    const timers = new Set(), cleanups = [], watched = [];
    const later = (fn, ms) => { const id = setTimeout(() => { timers.delete(id); fn(); }, ms); timers.add(id); return id; };
    const listen = (el, name, fn, options) => { el.addEventListener(name, fn, options); cleanups.push(() => el.removeEventListener(name, fn, options)); };
    const persist = (key, value) => { try { env.set(key, value); } catch (_) { state.storageError = true; } };
    const state = {
      identity: {id: '', key: '', part: 1}, classification: Content.classify({}),
      visit: null, visits: [], commentSeconds: 0, commentEntries: 0, commentReturns: 0,
      commentInside: false, commentCandidate: 0, commentLeft: 0, commentLastInput: 0, statsChanged: false,
      day:Core.dayKey(now()), lastActivity: now(), lastFocus: now(), lastTick: now(), lastRead: 0,
      pointer: {x: -1, y: -1}, comments: null, commentLookup: 0, folded: null,
      ended: false, mutedUntil: 0, panel: false, view: 'overview', serial: 0,
      pending: new Map(), shown: new Map(), notice: null, dialog: null,
      suppressUntil: 0, lastPanelUse: now(), lastSignificant: 0,
      observations: [], storageError: false, alive: true, snapshot: {},
      recentTitles: '', cancelLoad: null, metadata: {}, migrated: false
    };
    const store = new Core.Store({...env, id: uid(), onReset: () => resetAfterClear()});
    try { store.migrateLegacy(); } catch (_) { state.storageError = true; }
    const loader = Content.createLoader({...env,
      request: options => GM_xmlhttpRequest(options),
      onError: () => {state.storageError=true;}
    });
    const pageWindow = typeof unsafeWindow !== 'undefined' ? unsafeWindow : window;
    const format = s => { s = Math.max(0, Math.floor(s || 0)); return s >= 3600 ? `${Math.floor(s / 3600)}时${Math.floor(s % 3600 / 60)}分` : `${Math.floor(s / 60)}分${String(s % 60).padStart(2, '0')}秒`; };
    const escape = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
    const host = document.createElement('div'); host.id = 'bac3-host';
    const shadow = host.attachShadow({mode: 'open'});
    shadow.innerHTML = `<style>
      :host{all:initial;font:13px/1.5 -apple-system,BlinkMacSystemFont,"PingFang SC","Microsoft YaHei",sans-serif;color:#e8edf3;--opacity:.94}
      *{box-sizing:border-box}button,input,select{font:inherit}button{cursor:pointer;color:inherit;border:1px solid #ffffff24;background:#ffffff0b;border-radius:8px;padding:6px 9px}button:hover{background:#ffffff1e}button:focus-visible,input:focus-visible,select:focus-visible{outline:2px solid #95b7cf;outline-offset:2px}button.primary{background:#45677d}button:disabled{opacity:.5;cursor:default}
      #capsule{position:fixed;right:14px;top:145px;z-index:2147483000;display:flex;align-items:center;gap:8px;border:1px solid #ffffff29;border-radius:28px;padding:9px 13px;background:rgba(29,35,44,var(--opacity));box-shadow:0 5px 20px #0003;max-width:min(310px,calc(100vw - 12px));touch-action:none;user-select:none;cursor:grab;backdrop-filter:blur(12px)}#capsule:active{cursor:grabbing}#dot{width:6px;height:6px;background:#94bbaf;border-radius:50%;flex:none}#dot.warn{background:#d5b27f}#dot.paused{background:#929eac}#main{font-size:12px;font-weight:600;font-variant-numeric:tabular-nums}#sub{font-size:11px;color:#bac5d1;white-space:nowrap;text-overflow:ellipsis;overflow:hidden;max-width:250px}.compact #sub{display:none}
      #panel{position:fixed;z-index:2147483001;width:min(370px,calc(100vw - 20px));max-height:min(76vh,740px);overflow:auto;padding:15px;background:rgba(29,35,44,var(--opacity));border:1px solid #ffffff29;box-shadow:0 8px 32px #0005;border-radius:16px;backdrop-filter:blur(16px)}[hidden]{display:none!important}.head,.row{display:flex;align-items:center;justify-content:space-between;gap:10px}.head{margin-bottom:12px}.head strong{font-size:15px}p{margin:9px 0}.muted{font-size:11px;color:#acbac8}.grid{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin:12px 0}.stat{padding:10px;background:#ffffff08;border:1px solid #ffffff10;border-radius:10px}.stat span{display:block;font-size:11px;color:#acbac8}.stat b{font-size:18px;font-weight:600;font-variant-numeric:tabular-nums}.buttons{display:flex;gap:6px;flex-wrap:wrap;margin:10px 0}.line{border-top:1px solid #ffffff20;margin:12px 0}.signal{padding:9px;border-radius:9px;background:#d5b27f12;color:#d9c7ac;font-size:12px}label{display:flex;align-items:center;justify-content:space-between;gap:10px;margin:10px 0}input[type=number]{width:90px}input,select{padding:5px;border-radius:7px;border:1px solid #ffffff35;background:#303b48;color:#ecf1f5;max-width:190px}input[type=checkbox]{accent-color:#95b7cf}.barrow{display:grid;grid-template-columns:86px 1fr 65px;gap:6px;align-items:center;margin:8px 0;font-size:11px}.track{height:6px;background:#ffffff10;border-radius:4px;overflow:hidden}.bar{height:100%;background:#8aaebe;border-radius:4px}.week{display:flex;align-items:end;gap:6px;height:110px;margin:15px 0 6px}.day{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:end;height:100%;font-size:10px;gap:4px}.daybar{width:100%;background:#8aaebe;border-radius:4px 4px 0 0;min-height:1px}.scroll{overflow:auto}table{border-collapse:collapse;width:100%;font-size:11px}td,th{padding:6px 3px;border-bottom:1px solid #ffffff14;text-align:left}#toast{position:fixed;right:16px;top:75px;z-index:2147483002;max-width:min(370px,calc(100vw - 32px));background:#293540;border:1px solid #ffffff28;border-radius:12px;padding:12px;box-shadow:0 5px 20px #0003}#toast button{float:right;margin-left:8px}#backdrop{position:fixed;inset:0;display:grid;place-items:center;padding:20px;background:#10161b70;z-index:2147483003}#dialog{max-width:450px;width:100%;border-radius:16px;background:#242e39;padding:22px;border:1px solid #ffffff29;box-shadow:0 20px 80px #0007}#dialog h3{font-size:17px;margin:0 0 10px}#dialog p{white-space:pre-line}.full #capsule,.full #panel{display:none!important}.full:not(.strict) #toast,.full:not(.strict) #backdrop{display:none!important}
    </style><div id="shell"><button id="capsule" aria-label="展开B站注意力伴侣" aria-expanded="false"><i id="dot"></i><span><span id="main">B站注意力伴侣</span><div id="sub">正在初始化</div></span></button><section id="panel" hidden aria-label="B站注意力伴侣"><div class="head"><strong>注意力伴侣</strong><button data-action="close">收起</button></div><nav class="buttons"><button data-view="overview">概览</button><button data-view="report">报告</button><button data-view="settings">设置</button></nav><div id="body"></div></section><aside id="toast" hidden role="status"><button data-action="dismiss">关闭</button><span id="toast-text"></span></aside><div id="backdrop" hidden><section id="dialog" role="dialog" aria-modal="true" aria-labelledby="dialog-title"><h3 id="dialog-title"></h3><p id="dialog-text"></p><div class="buttons"><button class="primary" data-action="end">结束本次浏览</button><button data-action="fold">折叠／恢复评论</button><button data-action="pause">暂停当前播放</button><button data-action="mute">延后10分钟</button><button data-action="dismiss">继续浏览</button></div><p class="muted">结束会暂停当前播放并显示休息状态。可自行关闭标签页，或稍后恢复。</p></section></div></div>`;
    document.documentElement.append(host);
    const $ = id => shadow.getElementById(id);
    const shell = $('shell'), capsule = $('capsule'), panel = $('panel');
    let position = safeGet('bac3-position', null), drag = null, dragged = false;
    function place() {
      const width = capsule.getBoundingClientRect().width || 220;
      const x = Math.max(4, Math.min(innerWidth - width - 4, position?.x ?? innerWidth - width - 14));
      const y = Math.max(4, Math.min(innerHeight - 44, position?.y ?? 145));
      capsule.style.left = `${x}px`; capsule.style.top = `${y}px`; capsule.style.right = 'auto';
      panel.style.left = `${Math.max(10, Math.min(innerWidth - Math.min(370, innerWidth - 20) - 10, x + width - 370))}px`;
      const below = y + 58; panel.style.top = `${Math.max(8, Math.min(below, innerHeight - Math.min(innerHeight * .76, 740) - 8))}px`;
    }
    function setPanel(open, view = state.view) {
      state.panel = open; state.view = view; state.lastPanelUse = now();
      panel.hidden = !open; capsule.setAttribute('aria-expanded', String(open));
      if (open) { refreshSnapshot(); renderPanel(); place(); }
    }
    function updateUI() {
      const s = state.snapshot;
      $('main').textContent = `今日 ${format(s.siteSeconds)} · ${s.videoCount || 0}视频`;
      $('sub').textContent = state.ended ? '本次浏览已暂停 · 点击恢复' : state.notice?.message || (now() < state.mutedUntil ? '提醒已暂停 · 统计继续' : state.identity.id ? `${state.classification.category} · 评论 ${format(state.commentSeconds)}` : engaged() ? '有效浏览计时中 · 点击展开' : '计时暂停 · 点击展开');
      $('dot').className = state.ended || !engaged() ? 'paused' : state.notice ? 'warn' : '';
      capsule.title = `${state.classification.title || 'B站注意力伴侣'}\n连续 ${format(s.sessionSeconds)} · ${state.classification.expression || '无法判断'}\n评论 ${format(state.commentSeconds)} · 拖动调整位置`;
      shell.classList.toggle('compact', cfg.compact); host.style.setProperty('--opacity', cfg.opacity);
      if (state.panel && state.view === 'overview') {
        // 只更新数字；不每秒重建交互元素。
        for (const [key, value] of Object.entries({daily:format(s.siteSeconds),session:format(s.sessionSeconds),count:`${s.videoCount || 0} / ${s.openCount || 0}`,comments:format(s.commentSeconds),current:format(state.commentSeconds)})) {
          const el = shadow.querySelector(`[data-stat="${key}"]`); if (el) el.textContent = value;
        }
      }
    }
    function statsHTML() {
      const s = state.snapshot;
      return `<div class="grid"><div class="stat"><span>今日有效浏览</span><b data-stat="daily">${format(s.siteSeconds)}</b></div><div class="stat"><span>当前连续会话</span><b data-stat="session">${format(s.sessionSeconds)}</b></div><div class="stat"><span>有效视频／进入次数</span><b data-stat="count">${s.videoCount || 0} / ${s.openCount || 0}</b></div><div class="stat"><span>今日评论阅读（估计）</span><b data-stat="comments">${format(s.commentSeconds)}</b></div></div>`;
    }
    const opt = (arr, val) => arr.map(x => `<option value="${escape(x)}" ${x === val ? 'selected' : ''}>${escape(x)}</option>`).join('');
    const numberInput = (key, label, val, min=1, max=100000) => `<label>${label}<input type="number" name="${key}" value="${val}" min="${min}" max="${max}" required></label>`;
    const checkInput = (key,label) => `<label>${label}<input type="checkbox" name="${key}" ${cfg[key] ? 'checked' : ''}></label>`;
    function renderPanel() {
      const s = state.snapshot, c = state.classification;
      if (state.view === 'settings') {
        $('body').innerHTML = `<form id="settings"><label>浏览模式<select name="mode"><option value="normal" ${cfg.mode==='normal'?'selected':''}>普通</option><option value="learning" ${cfg.mode==='learning'?'selected':''}>学习（手动）</option><option value="entertainment" ${cfg.mode==='entertainment'?'selected':''}>娱乐</option></select></label><div class="buttons">${[15,30,45].map(m=>`<button type="button" data-budget="${m}">${m}分钟预算</button>`).join('')}</div>${numberInput('budgetSeconds','本次预算（分钟，0关闭）',cfg.budgetSeconds/60,0)}${numberInput('commentSoft','评论轻提醒（秒）',cfg.commentSoft,10,3600)}${numberInput('commentHard','评论强提醒（秒）',cfg.commentHard,20,7200)}${numberInput('sessionLimit','连续使用提醒（分钟）',cfg.sessionLimit/60)}${numberInput('dailyLimit','每日使用提醒（分钟）',cfg.dailyLimit/60)}${numberInput('quickCount','切换提醒视频数阈值',cfg.quickCount,3,40)}${numberInput('quickWindowSeconds','切换观察窗口（秒）',cfg.quickWindowSeconds,60,900)}${numberInput('shortVisitSeconds','短停留界线（秒）',cfg.shortVisitSeconds,6,120)}${numberInput('shortRatio','短停留比例（%）',cfg.shortRatio*100,30,100)}${numberInput('commentReturnCount','评论返回提醒次数',cfg.commentReturnCount,2,20)}${numberInput('reminderCooldown','相似提醒冷却（秒）',cfg.reminderCooldown,60,3600)}${numberInput('idleSeconds','无操作暂停（秒）',cfg.idleSeconds,15,600)}${numberInput('commentIdleSeconds','评论无操作暂停（秒）',cfg.commentIdleSeconds || 30,10,120)}${numberInput('autoCollapseSeconds','面板自动收起（秒，0关闭）',cfg.autoCollapseSeconds,0,300)}${numberInput('opacity','透明度（%）',Math.round(cfg.opacity*100),40,100)}<label>统计保留<select name="retentionDays"><option value="14" ${cfg.retentionDays===14?'selected':''}>14天</option><option value="30" ${cfg.retentionDays===30?'selected':''}>30天</option></select></label>${checkInput('autoFold','评论上限自动折叠')}${checkInput('useApi','读取B站视频信息')}${checkInput('topicHint','资料来源与标题信号提示')}${checkInput('compact','紧凑胶囊')}${checkInput('strictMode','严格模式：全屏允许强提醒')}<button class="primary" type="submit">保存设置</button><p class="muted">学习模式减少普通时间提示，保留评论、预算与快速切换提醒。预算预设也适用于普通／学习模式。资料信号不是质量、真假或政治立场判断。</p></form><div class="line"></div><button data-action="clear-confirm">清除统计…</button><p class="muted">只清除统计和v2统计备份；保留设置与手动分类。</p>`;
      } else if (state.view === 'report') { renderReport(); }
      else {
        $('body').innerHTML = `${statsHTML()}<div class="row"><b>${escape(c.category)}</b><span class="muted">${escape(c.expression)} · ${escape(c.confidence)}可信度</span></div><p class="muted">${escape(c.title || '首页、搜索、空间和直播也记录有效浏览。')}</p><p class="muted">依据：${escape((c.evidence || []).join('；') || '信息不足，保持未知')}</p>${c.signals?.length ? `<p class="signal">${escape(c.signals.join('；'))}。这些仅是进一步甄别的信号，请结合原始资料。</p>`:''}<p>本视频评论 <b data-stat="current">${format(state.commentSeconds)}</b> · ${state.commentEntries}次进入${state.folded?' · 已折叠':''}</p><p class="muted">${state.visit ? (state.visit.valid?'已确认有效浏览':`新进入，满${cfg.validSeconds}秒后确认`) + (state.visit.revisit?' · 回看':'') : '非普通视频页'} · ${cfg.mode==='learning'?'学习':cfg.mode==='entertainment'?'娱乐':'普通'}模式</p><p class="muted">${escape(state.notice?.message || (now()<state.mutedUntil?'提醒暂停中，统计仍运行':'提醒待命'))}</p><div class="buttons"><button data-action="fold">${state.folded?'恢复':'折叠'}评论</button><button data-action="mute">${now()<state.mutedUntil?'恢复提醒':'暂停提醒10分钟'}</button><button data-action="end">${state.ended?'恢复本次浏览':'结束本次浏览'}</button><button data-action="reset-session">重置连续会话</button></div>${state.identity.id ? `<details><summary>手动修正本视频分类</summary><form id="correction"><label>主题<select name="category">${opt(Content.categories,c.category)}</select></label><label>表达<select name="expression">${opt(Content.expressions,c.expression)}</select></label><button type="submit">本地记住修正</button> <button type="button" data-action="correction-reset">恢复自动分类</button></form></details>`:''}<p class="muted">${s.limited?'统计达到容量上限，部分细节已停止记录；请清理数据。':state.storageError?'本地存储失败，本次统计可能无法保存。':'全部判断在本地进行，不读取或保存评论正文与输入文本。'}</p>`;
      }
    }
    function renderReport() {
      const days = store.days(7,{},aggregationConfig()), s = state.snapshot;
      const max = Math.max(1, ...days.map(d=>d.siteSeconds || 0));
      const cats = Object.entries(s.categorySeconds || {}).sort((a,b)=>b[1]-a[1]);
      const bars = cats.map(([c,v])=>`<div class="barrow"><span>${escape(c)}</span><span class="track"><span class="bar" style="display:block;width:${Math.min(100,100*v/Math.max(1,s.siteSeconds))}%"></span></span><span>${format(v)}</span></div>`).join('');
      const first = days.slice(0,3).reduce((t,d)=>t+(d.siteSeconds||0),0)/3, last = days.slice(-3).reduce((t,d)=>t+(d.siteSeconds||0),0)/3;
      $('body').innerHTML = `${statsHTML()}<p class="muted">后台播放 ${format(s.backgroundSeconds)} · 页面闲置／失焦 ${format(s.idleSeconds)}</p><p>评论进入 ${s.commentEntries || 0}次 · 快速切换 ${s.quickSwitches || 0}次<br>连续切换提醒 ${s.bingeEpisodes || 0}次 · 提醒触发 ${s.reminders || 0}次<br>提醒后结束 ${s.exitEstimates || 0}次（估计，约${s.reminders?Math.round(100*(s.exitEstimates||0)/s.reminders):0}%）</p><p class="muted">观察到：折叠评论 ${s.interventions?.fold||0}次 · 离开视频 ${s.interventions?.leaveVideo||0}次 · 未继续切换 ${s.interventions?.stopSwitch||0}次 · 短期返回 ${s.interventions?.return||0}次。次数关联提醒，不代表心理状态或因果效果。</p><p class="muted">退出估计仅包括主动结束，或提醒后60秒内离开且至少60秒未观察到B站有效浏览。关闭浏览器无法可靠确认。闲置本身不作为干预成功。</p><strong>今日视频主题时长</strong>${bars || '<p class="muted">暂无有效观看数据</p>'}<div class="line"></div><strong>最近7天</strong><div class="week" role="img" aria-label="最近7天每日有效浏览时间">${days.map(d=>`<div class="day" title="${d.date} ${format(d.siteSeconds)}"><span>${Math.floor((d.siteSeconds||0)/60)}分</span><span class="daybar" style="height:${Math.round(75*(d.siteSeconds||0)/max)}px"></span><span>${d.date?.slice(5)}</span></div>`).join('')}</div><div class="scroll"><table><thead><tr><th>日期</th><th>视频</th><th>评论占比</th><th>切换提醒</th><th>主要类型</th></tr></thead><tbody>${days.map(d=>`<tr><td>${d.date?.slice(5)}</td><td>${d.videoCount||0}</td><td>${d.siteSeconds?Math.round(100*d.commentSeconds/d.siteSeconds):0}%</td><td>${d.bingeEpisodes||0}</td><td>${escape(Object.entries(d.categorySeconds||{}).sort((a,b)=>b[1]-a[1])[0]?.[0]||'—')}</td></tr>`).join('')}</tbody></table></div><p class="muted">后3日均值较前3日${Math.abs(last-first)<60?'大致持平':last>first?'增加':'减少'}${Math.abs(last-first)<60?'':`约${Math.round(Math.abs(last-first)/60)}分钟`}。缺失日期按0显示；时间更少不等于更健康。视频主题时长仅含普通视频页，非视频页不硬分主题。</p><button data-action="refresh">刷新报告</button>`;
    }

    function pageActive() { return document.visibilityState === 'visible' && document.hasFocus(); }
    let videoCache = [], videoCacheAt = 0;
    function playing(visibleOnly = false) {
      if (now()-videoCacheAt>(document.hidden?15000:3000) || !videoCache.length || videoCache.some(v=>!v.isConnected)) { videoCache=[...document.querySelectorAll('video')]; videoCacheAt=now(); }
      return videoCache.some(v=>{
        if (v.paused || v.ended || v.seeking || v.readyState < 2) return false;
        if (!visibleOnly) return true;
        const r=v.getBoundingClientRect(), w=Math.max(0,Math.min(r.right,innerWidth)-Math.max(0,r.left)), h=Math.max(0,Math.min(r.bottom,innerHeight)-Math.max(0,r.top));
        return r.width>100 && r.height>80 && w*h/Math.max(1,r.width*r.height)>.1;
      });
    }
    function engaged() { return !state.ended && pageActive() && (now()-state.lastActivity<cfg.idleSeconds*1000 || playing(true)); }
    function findComments() {
      if (state.folded?.el?.isConnected) return state.folded.el;
      if (state.comments?.isConnected && state.comments.getBoundingClientRect().height>0) return state.comments;
      if (now()-state.commentLookup<2500) return null;
      state.commentLookup=now();
      for (const sel of ['bili-comments','#commentapp','#comment','.comment-container','#comment-module']) {
        const el=document.querySelector(sel); if(el?.isConnected && el.getBoundingClientRect().height>0) return state.comments=el;
      }
      state.comments=null; return null;
    }
    function commentVisible() {
      const el=findComments(); if (!el || state.folded) return false;
      const r=el.getBoundingClientRect();
      const w=Math.max(0,Math.min(r.right,innerWidth)-Math.max(r.left,0)), h=Math.max(0,Math.min(r.bottom,innerHeight)-Math.max(r.top,0));
      return w*h>=innerWidth*innerHeight*.08;
    }
    function deepActive() { let a=document.activeElement; for(let i=0;i<16 && a?.shadowRoot?.activeElement;i++) a=a.shadowRoot.activeElement; return a; }
    function insideComments(el) {
      const hostEl=findComments();
      for(let node=el,i=0;node && i<20;i++) { if(node===hostEl || hostEl?.contains(node)) return true; node=node.parentElement || node.getRootNode?.().host; }
      return false;
    }
    function typingComment() {
      const a=deepActive(); return !!(a && insideComments(a) && ((!a.shadowRoot && a.tagName?.includes('-')) || a.matches('textarea,input,[contenteditable]:not([contenteditable="false"])') || a.closest('[contenteditable]:not([contenteditable="false"])')));
    }
    function foldComments(auto=false) {
      if(state.folded) return true;
      if(typingComment()) { if(!auto) localNotice('正在输入评论，暂不折叠。'); return false; }
      const el=findComments(); if(!el) return false;
      state.folded={el,value:el.style.getPropertyValue('display'),priority:el.style.getPropertyPriority('display')};
      el.style.setProperty('display','none','important'); state.commentInside=false;
      observeAction('fold'); if(state.panel && state.view==='overview') renderPanel(); return true;
    }
    function restoreComments() {
      const f=state.folded;
      if(f?.el?.isConnected) { if(f.value) f.el.style.setProperty('display',f.value,f.priority); else f.el.style.removeProperty('display'); }
      state.folded=null; state.commentCandidate=0; state.commentLastInput=now();
      if(state.panel && state.view==='overview') renderPanel();
    }
    function interaction(e) {
      if(e.composedPath?.().includes(host)) { state.lastPanelUse=now(); return; }
      // 移动鼠标只用于判断位置，不单独延长有效浏览。
      if(e.type==='pointermove' || e.type==='mousemove') { state.pointer={x:e.clientX,y:e.clientY}; return; }
      state.lastActivity=now();
      if(!state.identity.id) return;
      const el=findComments(); if(!el) return;
      const r=el.getBoundingClientRect(), p=state.pointer;
      const near=p.x>=r.left-32 && p.x<=r.right+32 && p.y>=r.top-50 && p.y<=r.bottom+50;
      const targeted=e.composedPath?.().some(n=>n?.nodeType===1 && insideComments(n));
      if(targeted || ((e.type==='wheel' || e.type==='touchstart') && near && commentVisible()) || ((e.type==='scroll' || e.type==='keydown') && commentVisible())) state.commentLastInput=now();
    }

    // 统一调度：模块只提交候选；实际显示时才计提醒次数、执行自动折叠。
    function requestNotice(item) {
      const key=item.key;
      const prior=(state.snapshot.events || []).filter(e=>e.type==='reminder' && (e.payload?.key===key || e.payload?.group===(item.group || key)));
      if(prior.some(e=>e.payload?.key===key) && !item.repeat)return;
      if(prior.some(e=>now()-e.at<cfg.reminderCooldown*1000))return;
      if(state.shown.has(key) && !item.repeat) return;
      if(now()-(state.shown.get(item.group || key)||0)<cfg.reminderCooldown*1000) return;
      state.pending.set(key,{...item,created:now(),expires:now()+(item.ttl || 90000)});
    }
    function closeNotice() {
      if(state.dialog) { state.shown.set(state.dialog.group || state.dialog.key,now()); }
      state.dialog=null; state.notice=null; $('backdrop').hidden=true; $('toast').hidden=true;
      state.suppressUntil=Math.max(state.suppressUntil,now()+30000);
      capsule.focus({preventScroll:true});
    }
    function localNotice(message) {
      state.notice={message,until:now()+7000}; updateUI();
    }
    function pump() {
      if(state.notice?.until && now()>state.notice.until && !state.dialog) { state.notice=null; $('toast').hidden=true; }
      for(const [k,v] of state.pending) if(v.expires<now() || (v.videoKey && v.videoKey!==state.identity.key)) state.pending.delete(k);
      if(state.ended || !pageActive() || state.dialog || now()<state.mutedUntil || now()<state.suppressUntil) return;
      if(document.fullscreenElement && !cfg.strictMode) return;
      const item=[...state.pending.values()].sort((a,b)=>b.priority-a.priority || a.created-b.created)[0];
      if(!item) return;
      const remoteReminders=store.rawShards(Core.dayKey(now())).flatMap(shard=>shard.events || []).filter(e=>e.type==='reminder');
      if(remoteReminders.some(e=>(e.payload?.key===item.key && !item.repeat) || (e.payload?.group===(item.group || item.key) && now()-e.at<cfg.reminderCooldown*1000))) {state.pending.delete(item.key);return;}
      // 用户正在写评论时，显著提醒和折叠均延迟，避免抢走输入焦点。
      if(item.level>1 && typingComment()) return;
      state.pending.delete(item.key); state.shown.set(item.key,now()); state.shown.set(item.group || item.key,now());
      state.notice={...item,until:now()+(item.level===1?12000:20000)};
      const event=store.event('reminder',{key:item.key,level:item.level,video:state.identity.id,group:item.group});
      store.flush();
      state.observations.push({id:event?.id || uid(),at:now(),video:state.identity.id,hiddenAt:0,exit:false,left:false,stop:false,hadSwitching:state.visits.filter(v=>now()-v.at<300000).length>=3});
      state.observations=state.observations.slice(-30);
      if(item.autoFold && cfg.autoFold) foldComments(true);
      if(item.level>=3) {
        state.dialog=item; $('dialog-title').textContent=item.title || '是否结束这一轮浏览？'; $('dialog-text').textContent=item.message;
        $('backdrop').hidden=false; shadow.querySelector('#dialog button')?.focus({preventScroll:true});
      } else if(item.level===2) { $('toast-text').textContent=item.message; $('toast').hidden=false; }
      state.suppressUntil=now()+(item.level>=3?120000:item.level===2?45000:15000);
      if(item.group==='binge') store.event('binge',{window:cfg.quickWindowSeconds});
      if(item.level>1) state.lastSignificant=now();
      updateUI();
    }
    function observeAction(action) {
      const targets=action==='exit'?state.observations.slice(-1):state.observations;
      for(const o of targets) if(now()-o.at<=60000 && !o[action]) {
        o[action]=true; store.event('intervention',{action,reminderId:o.id,estimated:action==='exit'});
      }
    }
    function checkObservation() {
      for(const o of state.observations) {
        if(o.hadSwitching && !o.stop && now()-o.at>=60000 && now()-o.at<180000 && engaged() && !state.visits.some(v=>v.at>o.at && v.at<=o.at+60000)) { o.stop=true; store.event('intervention',{action:'stopSwitch',reminderId:o.id}); }
        if(o.hiddenAt && !o.exit && now()-o.hiddenAt>=60000) {
          const recent=store.rawShards().flatMap(s=>s.intervals || []);
          // 存储模块的汇总结果覆盖其他标签页，前台仍有活动则不能算退出。
          const otherActive=recent.some(r=>(r.kind==='active' && r.end>o.hiddenAt+2000 && r.start<o.hiddenAt+60000));
          if(!otherActive && o===state.observations.filter(x=>x.hiddenAt).at(-1)) { o.exit=true; store.event('intervention',{action:'exit',reminderId:o.id,estimated:true,reason:'observed-away'}); }
          o.hiddenAt=0;
        }
      }
    }
    function thresholds() {
      const v=state.visit, s=state.snapshot;
      if(v && state.commentSeconds>=cfg.commentHard) requestNotice({key:`comment-hard-${v.token}-${cfg.commentHard}`,group:'comment-hard',priority:100,level:3,videoKey:state.identity.key,autoFold:true,title:'评论阅读已达设定上限',message:`当前视频评论累计约${format(state.commentSeconds)}。是否还有新信息值得继续阅读？可先折叠，之后随时恢复。`});
      else if(v && state.commentSeconds>=cfg.commentSoft) requestNotice({key:`comment-soft-${v.token}-${cfg.commentSoft}`,group:'comment-soft',priority:75,level:1,videoKey:state.identity.key,message:`评论已读约${format(state.commentSeconds)}。可以先回到视频，稍后再决定是否继续。`});
      if(v && state.commentEntries>=cfg.commentReturnCount) requestNotice({key:`comment-return-${v.token}-${cfg.commentReturnCount}`,group:'comment-return',priority:85,level:2,videoKey:state.identity.key,message:`你已${state.commentEntries}次进入这个评论区。这里是否还有值得获取的新信息？${state.classification.topic?'评论区也不能代表整体民意。':''}`});
      const shared=new Map();
      for(const e of s.events || []) {
        if(e.at<now()-900000 || !e.payload?.token)continue;
        const p=e.payload;
        if(e.type==='open')shared.set(p.token,{...p,id:p.video,at:e.at,closed:false,seconds:0});
        if(e.type==='visitEnd') {const visit=shared.get(p.token);if(visit)Object.assign(visit,p,{closed:true,end:e.at});}
      }
      for(const local of state.visits)shared.set(local.token,local);
      const behavior=Core.detectBehavior([...shared.values()],cfg,now());
      state.behavior=behavior;
      if(behavior.level) requestNotice({key:`binge-${Math.floor(now()/(cfg.quickWindowSeconds*1000))}`,group:'binge',repeat:true,priority:90,level:behavior.level,message:`${behavior.reasons.join('，')}。${behavior.message}`});
      const topical=[...shared.values()].filter(x=>x.topic && now()-x.at<900000 && x.closed && x.seconds<cfg.shortVisitSeconds);
      if(topical.length>=Math.max(3,cfg.quickCount-2) && state.commentEntries>=cfg.commentReturnCount) requestNotice({key:`combined-${Core.dayKey(now())}-${state.identity.id}`,group:'combined',priority:95,level:3,title:'是否先暂停这一轮？',message:'最近多次短暂停留于公共议题视频，并反复进入评论区。现在是否还有想主动获取的新信息？'});
      const budget=cfg.budgetSeconds;
      if(budget>0 && (s.sessionSeconds||0)>=budget) requestNotice({key:`budget-${budget}-${sessionToken()}`,group:'budget',priority:80,level:3,title:'本次浏览预算已到',message:`本次有效浏览已达${format(budget)}。可以现在结束，或选择继续。`});
      else if(budget>0 && (s.sessionSeconds||0)>=budget*.8) requestNotice({key:`budget-near-${budget}-${sessionToken()}`,group:'budget-near',priority:65,level:1,message:`本次预算还剩约${format(budget-(s.sessionSeconds||0))}。`});
      if(cfg.mode!=='learning' && (s.sessionSeconds||0)>=cfg.sessionLimit) requestNotice({key:`session-${cfg.sessionLimit}-${sessionToken()}`,group:'session',priority:50,level:1,message:`你已连续有效浏览约${format(s.sessionSeconds)}。是否还记得打开B站的目的？`});
      if((s.siteSeconds||0)>=cfg.dailyLimit) requestNotice({key:`daily-${Core.dayKey(now())}-${cfg.dailyLimit}`,group:'daily',priority:55,level:1,message:`今日有效浏览约${format(s.siteSeconds)}。可以看看报告，再决定接下来的安排。`});
      for(const count of cfg.videoMilestones || []) if((s.videoCount||0)>=count && cfg.mode!=='learning') requestNotice({key:`count-${Core.dayKey(now())}-${count}`,group:'count',priority:30,level:1,message:`今天已有${count}个视频达到有效浏览门槛。下一条仍是你主动想看的吗？`});
    }
    let manualSessionToken=0;
    function sessionToken() { return `${manualSessionToken}-${state.snapshot.sessionId || 'pending'}`; }

    function correction() { try { return Content.getCorrection(env,state.identity.id); } catch (_) { return null; } }
    function applyMetadata(meta, serial) {
      if(!meta) return;
      if(serial!==state.serial || !state.identity.id) return;
      state.metadata={...state.metadata,...Object.fromEntries(Object.entries(meta).filter(([,v])=>v!=='' && v!=null))};
      const previous=state.classification;
      state.classification=Content.classify(state.metadata,correction());
      if(state.visit){state.visit.category=state.classification.category;state.visit.topic=state.classification.topic;state.visit.expression=state.classification.expression;}
      if(state.classification.category!==previous.category || state.classification.title!==previous.title) { if(state.panel && state.view==='overview') renderPanel(); updateUI(); }
      const c=state.classification;
      if(cfg.topicHint && (c.topic || c.signals?.length)) requestNotice({key:`content-${state.identity.id}`,group:'content',priority:10,level:1,videoKey:state.identity.key,message:c.topic?'涉及公共议题时，可以留意原始资料和出处。评论区不能代表整体民意。':'标题中有值得进一步甄别的措辞。可结合内容与来源再判断。'});
    }
    let headingObserver=null, observedHeading=null, headingScheduled=false;
    function readPageMetadata(serial=state.serial, allowTitle=true) {
      if(!state.identity.id || serial!==state.serial) return;
      const heading=document.querySelector('h1.video-title, h1[title], #viewbox_report h1');
      if(heading!==observedHeading) {
        headingObserver?.disconnect();observedHeading=heading;
        if(heading) {headingObserver=new MutationObserver(()=>{if(!headingScheduled){headingScheduled=true;later(()=>{headingScheduled=false;readPageMetadata(state.serial,true);},120);}});headingObserver.observe(heading,{childList:true,subtree:true,characterData:true,attributes:true,attributeFilter:['title']});}
      }
      state.lastMetadataRead=now();
      try { const meta=Content.readMetadata(document,pageWindow,state.identity.id,{allowTitle,previousTitle:state.routePreviousTitle}); if(meta.title || meta.area || meta.tags) applyMetadata(meta,serial); } catch (_) {}
    }
    function closeVisit() {
      if(!state.visit || state.visit.closed) return;
      state.visit.closed=true; state.visit.end=now();
      store.event('visitEnd',{token:state.visit.token,video:state.visit.id,seconds:state.visit.seconds,source:state.visit.source,expression:state.visit.expression,category:state.visit.category,topic:state.visit.topic});
      if(state.visit.seconds<cfg.shortVisitSeconds) store.event('quickSwitch',{video:state.visit.id,seconds:state.visit.seconds,source:state.visit.source});
      observeAction('leaveVideo');
    }
    let currentRoute='', routeSource=/^https:\/\/search\.bilibili\.com\//.test(document.referrer)?'search':'direct', clickTitle='', previousDOMTitle='';
    function checkRoute(force=false) {
      const next=Content.getVideoIdentity(location.href), route=location.pathname;
      if(!next.id && !state.identity.id && route===currentRoute && !force)return false;
      if(!force && next.key===state.identity.key && route===currentRoute) return false;
      account(now());
      const oldTitle=state.classification.title;
      closeVisit(); restoreComments(); state.cancelLoad?.(); state.serial++;
      state.routePreviousTitle=oldTitle;
      state.identity=next; currentRoute=route; state.commentSeconds=0; state.commentEntries=0; state.commentReturns=0; state.commentInside=false; state.commentCandidate=0; state.commentLeft=0; state.comments=null; state.commentLookup=0; state.commentLastInput=0;
      state.metadata={}; state.classification=Content.classify({});
      for(const [k,item] of state.pending) if(item.videoKey) state.pending.delete(k);
      if(state.dialog?.videoKey) closeNotice();
      if(next.id) {
        const prior=state.snapshot.validVideos || {};
        const v={token:uid(),id:next.id,key:next.key,part:next.part,at:now(),seconds:0,daySeconds:0,day:Core.dayKey(now()),valid:false,revisit:!!prior[next.id],source:routeSource,expression:'无法判断',closed:false};
        state.visit=v; state.visits.push(v); state.visits=state.visits.filter(x=>now()-x.at<Math.max(900000,cfg.quickWindowSeconds*1000));
        store.event('open',{token:v.token,video:next.id,part:next.part,source:routeSource,revisit:v.revisit});
        store.flush();
        // 返回同一视频时恢复当日评论累计，避免刷新或反复进出绕过上限。
        const canonical=id=>{try{return Content.canonical(env,id);}catch(_){return id;}};
        const currentID=canonical(next.id), shards=store.rawShards(Core.dayKey(now()));
        state.commentSeconds=Core.unionDuration(shards.flatMap(shard=>shard.intervals || []).filter(r=>r.kind==='comment' && canonical(r.video)===currentID));
        state.commentEntries=shards.flatMap(shard=>shard.events || []).filter(e=>e.type==='commentEnter' && canonical(e.payload?.video)===currentID).length;

        // 先清空旧状态；只有点击目标标题或匹配的视频结构信息可立即采用。
        if(clickTitle) applyMetadata({title:clickTitle,source:'点击的视频链接'},state.serial);
        readPageMetadata(state.serial,force);
        if(cfg.useApi) { const serial=state.serial; state.cancelLoad=loader.load(next.id,meta=>applyMetadata(meta,serial)); }
        const serial=state.serial; [120,450,1200,3000,7000].forEach(ms=>later(()=>readPageMetadata(serial,true),ms));
      } else state.visit=null;
      previousDOMTitle=document.title; routeSource=location.hostname==='search.bilibili.com'?'search':'direct'; clickTitle='';
      refreshSnapshot(); if(state.panel) renderPanel(); updateUI(); return true;
    }
    function aggregationConfig() {
      const aliases={}; try { for(const key of env.list()) if(key.startsWith('bac3-alias:')) aliases[key.slice(11)]=safeGet(key,''); } catch(_) {}
      return {...cfg,aliases};
    }
    function refreshSnapshot() { try { state.snapshot=store.read(Core.dayKey(now()),now(),{},aggregationConfig()); state.storageError=state.storageError || !!store.error;state.lastRead=now(); } catch (_) { state.storageError=true; } }
    function resetAfterClear() {
      restoreComments();state.visits=[]; state.observations=[]; state.pending.clear(); state.shown.clear(); state.commentSeconds=0; state.commentEntries=0; state.commentInside=false; manualSessionToken++;
      if(state.visit) { state.visit.seconds=0;state.visit.daySeconds=0;state.visit.valid=false;state.visit.day=Core.dayKey(now()); }
      closeNotice(); state.lastTick=now(); refreshSnapshot(); if(state.panel) renderPanel(); updateUI();
    }
    function account(t) {
      const currentDay=Core.dayKey(t);
      if(state.day!==currentDay) {state.day=currentDay;state.commentSeconds=0;state.commentEntries=0;state.commentReturns=0;state.statsChanged=true;}
      // 定时器休眠、系统睡眠不补算；按真实可观测短区间记录。
      const start=state.lastTick, delta=Math.max(0,Math.min(2000,t-start)); state.lastTick=t;
      const active=engaged(), bg=!active && !state.ended && playing(false);
      if(delta>0 && !state.ended) {
        const v=state.visit, category=v?state.classification.category:'';
        store.recordInterval(t-delta,t,active?'active':bg?'background':'idle',category,state.identity.id,state.lastFocus);
        if(active && v) {
          v.seconds+=delta/1000;v.expression=state.classification.expression;
          for(const piece of Core.splitInterval(t-delta,t)) {
            if(v.day!==piece.date) {v.day=piece.date;v.daySeconds=0;v.valid=false;}
            v.daySeconds+=(piece.end-piece.start)/1000;
            if(!v.valid && v.daySeconds>=cfg.validSeconds) {v.valid=true;store.event('valid',{video:v.id,category:state.classification.category},piece.end-1);state.statsChanged=true;}
          }
        }
        const reading=active && !!v && commentVisible() && t-state.commentLastInput<(cfg.commentIdleSeconds||30)*1000;
        if(reading) {
          if(!state.commentCandidate) state.commentCandidate=t;
          state.commentLeft=0;
          if(!state.commentInside && t-state.commentCandidate>=1200) { state.commentInside=true;state.commentEntries++;store.event('commentEnter',{video:state.identity.id}); if(state.commentSeconds>=cfg.commentSoft) {state.commentReturns++;store.event('commentReturn',{video:state.identity.id});} }
          if(state.commentInside) {state.commentSeconds+=Core.splitInterval(t-delta,t).filter(p=>p.date===currentDay).reduce((sum,p)=>sum+(p.end-p.start)/1000,0);store.recordInterval(t-delta,t,'comment',category,state.identity.id,state.lastFocus);}
        } else { state.commentCandidate=0; if(!state.commentLeft) state.commentLeft=t; if(t-state.commentLeft>2500) state.commentInside=false; }
      }
    }
    function tick() {
      if(!state.alive) return;
      const t=now(); checkRoute();account(t);
      if(pageActive() && state.identity.id && !state.classification.title && t-(state.lastMetadataRead || 0)>5000)readPageMetadata(state.serial,true);
      if(state.shown.size>1000) for(const key of [...state.shown.keys()].slice(0,state.shown.size-1000))state.shown.delete(key);
      if(t-state.lastRead>=5000 || state.statsChanged) {store.flush();refreshSnapshot();state.statsChanged=false;}
      if(engaged()) { thresholds();pump();checkObservation(); } else checkObservation();
      if(state.panel && cfg.autoCollapseSeconds>0 && t-state.lastPanelUse>cfg.autoCollapseSeconds*1000 && !panel.matches(':hover') && !shadow.activeElement?.closest('#panel')) setPanel(false);
      updateUI();
    }

    function updateConfig(next) {
      const old=cfg; cfg=Core.normalizeConfig({...cfg,...next}); persist('bac3-settings',cfg);
      state.pending.clear();state.suppressUntil=now()+2000;
      if(!cfg.useApi) {state.cancelLoad?.();state.serial++;}
      if(!old.useApi && cfg.useApi && state.identity.id) {const serial=++state.serial;state.cancelLoad=loader.load(state.identity.id,meta=>applyMetadata(meta,serial));}
      if(cfg.retentionDays!==old.retentionDays) store.cleanup(cfg.retentionDays);
      fullscreen(); if(state.panel) renderPanel();updateUI();return cfg;
    }
    function endBrowsing() {
      if(state.ended) {for(const o of state.observations)if(o.exit && !o.returned && now()-o.at<300000){o.returned=true;store.event('intervention',{action:'return',reminderId:o.id});}state.ended=false;state.lastActivity=now();state.lastTick=now();localNotice('已恢复本次浏览。');}
      else {observeAction('exit');state.ended=true;document.querySelectorAll('video').forEach(v=>{try{v.pause();}catch(_){}});foldComments(true);closeNotice();store.event('sessionReset',{reason:'user-end'});store.flush();localNotice('本次浏览已暂停。可自行关闭标签页，或点击恢复。');}
      refreshSnapshot();if(state.panel)renderPanel();updateUI();
    }
    function fullscreen() {
      const full=!!document.fullscreenElement;shell.classList.toggle('full',full);shell.classList.toggle('strict',cfg.strictMode);
      if(full) {setPanel(false);if(!cfg.strictMode){$('toast').hidden=true;if(state.dialog)closeNotice();}}
      // 严格模式只有用户启用后才把提示放入原生全屏树。
      const target=full && cfg.strictMode?document.fullscreenElement:document.documentElement;
      if(host.parentNode!==target) {try{target.appendChild(host);}catch(_){}}
    }
    async function action(name) {
      state.lastPanelUse=now();
      if(name==='close')setPanel(false);
      else if(name==='dismiss')closeNotice();
      else if(name==='fold') {if(state.folded)restoreComments();else if(!foldComments())localNotice('暂未找到评论区，或正在输入。');}
      else if(name==='mute') {state.mutedUntil=now()<state.mutedUntil?0:now()+600000;state.pending.clear();closeNotice();localNotice(state.mutedUntil?'提醒暂停10分钟，统计继续。':'提醒已恢复。');}
      else if(name==='pause') {document.querySelectorAll('video').forEach(v=>{try{v.pause();}catch(_){}});localNotice('已暂停当前页面可控制的视频。自动连播开关无法可靠控制，请在播放器内手动关闭。');closeNotice();}
      else if(name==='end')endBrowsing();
      else if(name==='reset-session') {store.event('sessionReset',{reason:'manual'});manualSessionToken++;state.shown.clear();state.pending.clear();refreshSnapshot();renderPanel();}
      else if(name==='refresh') {refreshSnapshot();renderPanel();}
      else if(name==='correction-reset') {Content.setCorrection(env,state.identity.id,null);applyMetadata(state.metadata,state.serial);renderPanel();}
      else if(name==='clear-confirm') {$('body').innerHTML='<p>清除所有标签页中的v3统计和v2统计备份？保留设置及手动分类。此操作无法撤销。</p><div class="buttons"><button data-action="clear" class="primary">确认清除统计</button><button data-view="settings">取消</button></div>';}
      else if(name==='clear') {if(!store.clear()){localNotice('清除失败，请检查油猴存储权限或容量。');return;}try{env.del('bac2-data');env.del('bac2-session');}catch(_){} resetAfterClear();localNotice('统计已清除，已通知其他标签页。');}
    }
    listen(shadow,'click',e=>{const b=e.target.closest('button');if(!b)return;const a=b.dataset.action;if(a)action(a);if(b.dataset.view)setPanel(true,b.dataset.view);if(b.dataset.budget){const input=shadow.querySelector('[name="budgetSeconds"]');if(input)input.value=b.dataset.budget;}});
    listen(shadow,'submit',e=>{
      e.preventDefault();const f=e.target;
      if(f.id==='settings') {const values=Object.fromEntries(new FormData(f));for(const key of ['autoFold','useApi','topicHint','compact','strictMode'])values[key]=f.elements[key].checked;for(const key of ['budgetSeconds','sessionLimit','dailyLimit'])values[key]=Number(values[key])*60;values.opacity=Number(values.opacity)/100;values.shortRatio=Number(values.shortRatio)/100;if(Number(values.commentHard)<=Number(values.commentSoft)){localNotice('强提醒时间必须大于轻提醒。');return;}updateConfig(values);localNotice('设置已保存。');}
      if(f.id==='correction') {const values=Object.fromEntries(new FormData(f));Content.setCorrection(env,state.identity.id,values);applyMetadata(state.metadata,state.serial);if(state.visit?.valid)store.event('valid',{video:state.identity.id,category:state.classification.category});renderPanel();localNotice('已在本地记住修正；之后的时长使用新分类。');}
    });
    listen(capsule,'pointerdown',e=>{if(e.button!==0)return;const r=capsule.getBoundingClientRect();drag={x:e.clientX,y:e.clientY,left:r.left,top:r.top};dragged=false;capsule.setPointerCapture?.(e.pointerId);});
    listen(capsule,'pointermove',e=>{if(!drag)return;const dx=e.clientX-drag.x,dy=e.clientY-drag.y;if(Math.hypot(dx,dy)>4)dragged=true;if(dragged){position={x:drag.left+dx,y:drag.top+dy};place();}});
    listen(capsule,'pointerup',()=>{if(dragged)persist('bac3-position',position);drag=null;});
    listen(capsule,'pointercancel',()=>{drag=null;dragged=true;});
    listen(capsule,'click',()=>{if(dragged){dragged=false;return;}if(state.ended)endBrowsing();setPanel(!state.panel);});
    listen(shadow,'pointermove',()=>{state.lastPanelUse=now();},{passive:true});
    listen(shadow,'keydown',e=>{state.lastPanelUse=now();if(e.key==='Escape'){closeNotice();setPanel(false);}if(e.key==='Tab' && state.dialog){const bs=[...shadow.querySelectorAll('#dialog button')];if(e.shiftKey && shadow.activeElement===bs[0]){e.preventDefault();bs.at(-1).focus();}else if(!e.shiftKey && shadow.activeElement===bs.at(-1)){e.preventDefault();bs[0].focus();}}});
    ['scroll','wheel','keydown','pointerdown','touchstart','pointermove'].forEach(type=>listen(window,type,interaction,{passive:true,capture:true}));
    listen(window,'click',e=>{
      const a=e.composedPath?.().find(n=>n?.tagName==='A' && n.href);if(!a)return;
      const id=Content.getVideoIdentity(a.href);if(!id.id)return;
      routeSource=location.hostname==='search.bilibili.com'?'search':/recommend|rec-list|video-card/i.test(a.closest('[class]')?.className || '')?'recommendation':'link';
      clickTitle=insideComments(a)?'':(a.getAttribute('title') || a.querySelector('[title]')?.getAttribute('title') || a.textContent || '').trim().slice(0,180);
      later(()=>checkRoute(),0);
    },{capture:true,passive:true});
    function transition() {state.lastTick=now();store.flush();refreshSnapshot();updateUI();}
    listen(window,'focus',()=>{state.lastFocus=now();state.lastActivity=now();transition();});
    listen(window,'blur',transition);
    listen(document,'visibilitychange',()=>{
      if(document.visibilityState==='hidden')for(const o of state.observations)if(now()-o.at<=60000)o.hiddenAt=now();
      else {for(const o of state.observations)if(o.exit && !o.returned && now()-o.at<300000){o.returned=true;store.event('intervention',{action:'return',reminderId:o.id});}state.lastFocus=now();}
      transition();checkObservation();
    });
    listen(document,'fullscreenchange',fullscreen);listen(window,'resize',place);
    listen(window,'pagehide',()=>{account(now());closeVisit();store.flush();});listen(window,'pageshow',e=>{state.lastTick=now();checkRoute(!!e.persisted);});
    ['popstate','hashchange'].forEach(type=>listen(window,type,()=>checkRoute()));
    for(const name of ['pushState','replaceState']) {
      try{const original=pageWindow.history[name];const wrapped=function(...args){const result=original.apply(this,args);checkRoute();return result;};pageWindow.history[name]=wrapped;cleanups.push(()=>{if(pageWindow.history[name]===wrapped)pageWindow.history[name]=original;});}catch(_){}
    }
    if(pageWindow.navigation?.addEventListener)listen(pageWindow.navigation,'navigatesuccess',()=>checkRoute());
    const titleEl=document.querySelector('title');
    if(titleEl){let scheduled=false;const obs=new MutationObserver(()=>{if(scheduled)return;scheduled=true;later(()=>{scheduled=false;checkRoute();readPageMetadata(state.serial,true);},120);});obs.observe(titleEl,{childList:true,subtree:true,characterData:true});watched.push(obs);}
    function syncSettings() {const incoming=Core.normalizeConfig(safeGet('bac3-settings',cfg));const old=cfg;cfg=incoming;store.sync();refreshSnapshot();if(old.useApi!==cfg.useApi){state.cancelLoad?.();const serial=++state.serial;if(cfg.useApi && state.identity.id)state.cancelLoad=loader.load(state.identity.id,meta=>applyMetadata(meta,serial));}if(old.strictMode!==cfg.strictMode)fullscreen();updateUI();}
    let signalScheduled=false;
    if(typeof GM_addValueChangeListener==='function')for(const key of ['bac3-signal','bac3-epoch','bac3-settings'])try{const id=GM_addValueChangeListener(key,(_k,_o,_v,remote)=>{if(!remote)return;if(_k==='bac3-signal'){if(!signalScheduled){signalScheduled=true;later(()=>{signalScheduled=false;syncSettings();},500);}}else syncSettings();});cleanups.push(()=>GM_removeValueChangeListener(id));}catch(_){}
    try{const id=GM_registerMenuCommand('打开B站注意力伴侣 v3',()=>setPanel(true));cleanups.push(()=>{if(typeof GM_unregisterMenuCommand==='function')GM_unregisterMenuCommand(id);});}catch(_){}
    // 即使 history 包装被站点替换，1秒 URL 比较仍能恢复；只检查字符串，不扫描DOM。
    const loop=setInterval(()=>{try{tick();}catch(e){console.warn('[B站注意力伴侣]',e);state.storageError=true;}},1000);
    cleanups.push(()=>clearInterval(loop));
    const housekeeping=setInterval(()=>{try{store.sync();refreshSnapshot();store.cleanup(cfg.retentionDays);loader.cleanup?.();}catch(_){state.storageError=true;}},60000);cleanups.push(()=>clearInterval(housekeeping));
    store.cleanup(cfg.retentionDays);refreshSnapshot();checkRoute(true);place();fullscreen();updateUI();
    function destroy() {state.alive=false;store.flush();state.cancelLoad?.();loader.destroy?.();headingObserver?.disconnect();restoreComments();timers.forEach(clearTimeout);watched.forEach(o=>o.disconnect());cleanups.reverse().forEach(fn=>{try{fn();}catch(_){}});host.remove();}
    return {state,store,tick,checkRoute,updateConfig,refreshSnapshot,requestNotice,pump,foldComments,restoreComments,typingComment,setPanel,action,destroy,host,get config(){return cfg;}};
  }
  // 同一文档重复注入不重复注册定时器；测试入口只有主动预置时才暴露。
  if (typeof window !== 'undefined' && typeof document !== 'undefined') {
    if (!document.getElementById('bac3-host')) {
      const app = createApp();
      if (window.__BAC_TEST_HOOK__ && typeof window.__BAC_TEST_HOOK__ === 'object') Object.assign(window.__BAC_TEST_HOOK__, {Core,Content,app,createApp});
    }
  }
})();
