/* ================= النواة المشتركة (الخادم + وضع التجربة) ================= */
var TABLES = {
  users: ['id','role','username','name','class','classes','salt','hash','key','active','created','lastLogin'],
  answers: ['time','userId','mode','qid','subject','domain','skill','correct','ms'],
  characters: ['id','name','img'],
  settings: ['key','value']
};
function sha256raw(ascii) {
  function rr(v, a) { return (v >>> a) | (v << (32 - a)); }
  var maxWord = Math.pow(2, 32), i, j, result = '', words = [], bitLen = ascii.length * 8;
  var hash = [], k = [], pc = 0, isComp = {};
  for (var cand = 2; pc < 64; cand++) {
    if (!isComp[cand]) {
      for (i = 0; i < 313; i += cand) isComp[i] = cand;
      hash[pc] = (Math.pow(cand, .5) * maxWord) | 0;
      k[pc++] = (Math.pow(cand, 1 / 3) * maxWord) | 0;
    }
  }
  hash = hash.slice(0, 8);
  ascii += '\x80';
  while (ascii.length % 64 - 56) ascii += '\x00';
  for (i = 0; i < ascii.length; i++) { j = ascii.charCodeAt(i); words[i >> 2] |= j << ((3 - i) % 4) * 8; }
  words[words.length] = ((bitLen / maxWord) | 0);
  words[words.length] = bitLen;
  for (j = 0; j < words.length;) {
    var w = words.slice(j, j += 16), old = hash;
    hash = hash.slice(0, 8);
    for (i = 0; i < 64; i++) {
      var w15 = w[i - 15], w2 = w[i - 2], a = hash[0], e = hash[4];
      var t1 = hash[7] + (rr(e, 6) ^ rr(e, 11) ^ rr(e, 25)) + ((e & hash[5]) ^ ((~e) & hash[6])) + k[i] +
        (w[i] = (i < 16) ? w[i] : (w[i - 16] + (rr(w15, 7) ^ rr(w15, 18) ^ (w15 >>> 3)) + w[i - 7] + (rr(w2, 17) ^ rr(w2, 19) ^ (w2 >>> 10))) | 0);
      var t2 = (rr(a, 2) ^ rr(a, 13) ^ rr(a, 22)) + ((a & hash[1]) ^ (a & hash[2]) ^ (hash[1] & hash[2]));
      hash = [(t1 + t2) | 0].concat(hash);
      hash[4] = (hash[4] + t1) | 0;
    }
    for (i = 0; i < 8; i++) hash[i] = (hash[i] + old[i]) | 0;
  }
  for (i = 0; i < 8; i++) for (j = 3; j + 1; j--) { var b = (hash[i] >> (j * 8)) & 255; result += ((b < 16) ? 0 : '') + b.toString(16); }
  return result;
}
function sha256u(s) { return sha256raw(unescape(encodeURIComponent(String(s)))); }

function aggregate(rows) {
  var A = {};
  rows.forEach(function (r) {
    var id = String(r.studentId);
    var a = A[id] || (A[id] = { pre: { d: {}, k: {} }, post: { d: {}, k: {} }, game: { d: {}, k: {} }, days: {}, last: 0 });
    var m = a[r.mode]; if (!m) return;
    var c = Number(r.correct) ? 1 : 0;
    var d = m.d[r.domain] || (m.d[r.domain] = [0, 0]); d[0] += c; d[1]++;
    var k = m.k[r.skill] || (m.k[r.skill] = [0, 0]); k[0] += c; k[1]++;
    if (r.mode === 'game') { var t = new Date(r.time).getTime(); if (t > a.last) a.last = t; a.days[new Date(t).toISOString().slice(0, 10)] = 1; }
  });
  Object.keys(A).forEach(function (id) { A[id].days = Object.keys(A[id].days).length; });
  return A;
}
function statusOf(rows) {
  var didPre = rows.some(function (r) { return r.mode === 'pre'; }), didPost = rows.some(function (r) { return r.mode === 'post'; });
  var k = {};
  rows.forEach(function (r) { if (r.mode === 'post' || !r.skill) return; var x = k[r.skill] || (k[r.skill] = [0, 0]); x[0] += Number(r.correct) ? 1 : 0; x[1]++; });
  var weak = Object.keys(k).filter(function (s) { return k[s][1] >= 2 && k[s][0] / k[s][1] < .7; })
    .sort(function (a, b) { return k[a][0] / k[a][1] - k[b][0] / k[b][1]; }).slice(0, 3);
  return { didPre: didPre, didPost: didPost, weak: weak };
}

function makeAPI(DB) {
  var norm = function (s) { return String(s == null ? '' : s).trim().toLowerCase(); };
  var iso = function (v) { if (!v) return ''; var d = new Date(v); return isNaN(d.getTime()) ? '' : d.toISOString(); };
  var rid = function (n) { return DB.uuid().replace(/-/g, '').slice(0, n || 12); };
  var hashPw = function (pw, salt) { return sha256u(String(salt) + '|' + String(pw)); };
  var genPw = function () { return String(1000 + Math.floor(Math.random() * 9000)); };
  var cleanUser = function (u) { return norm(u).replace(/\s+/g, ''); };
  var cleanClasses = function (c) { return String(c || '').split(/[,،]/).map(function (x) { return x.trim(); }).filter(Boolean).join(','); };
  function err(code) { return new Error(code); }
  function setting(k) { var r = DB.rows('settings').find(function (x) { return x.key === k; }); return r ? String(r.value) : ''; }
  function setSetting(k, v) { if (!DB.update('settings', 'key', k, { value: v })) DB.insert('settings', { key: k, value: v }); }
  function guard(k) {
    var n = Number(DB.cacheGet('f_' + k) || 0);
    if (n >= 5) throw err('LOCK');
    return { fail: function () { DB.cachePut('f_' + k, String(n + 1), 600); } };
  }
  function users() { return DB.rows('users'); }
  function byId(id) { return users().find(function (u) { return String(u.id) === String(id); }); }
  function isActive(u) { return String(u.active) !== 'no'; }
  function sess(token, roles) {
    var v = DB.cacheGet('t_' + token); if (!v) throw err('SESSION');
    var s = JSON.parse(v); if (roles && roles.indexOf(s.role) < 0) throw err('FORBIDDEN');
    return s;
  }
  function myClasses(u) { return u.role === 'admin' ? null : String(u.classes || '').split(',').map(function (x) { return x.trim(); }).filter(Boolean); }
  function canClass(s, cls) { if (s.role === 'admin') return true; var u = byId(s.id); return (myClasses(u) || []).map(norm).indexOf(norm(cls)) >= 0; }
  function usernameFree(un, exceptId) { return !users().some(function (u) { return norm(u.username) === un && String(u.id) !== String(exceptId || ''); }); }
  function startSession(u) {
    var t = DB.uuid();
    DB.cachePut('t_' + t, JSON.stringify({ id: String(u.id), role: String(u.role) }), 21600);
    DB.update('users', 'id', u.id, { lastLogin: DB.now() });
    return t;
  }
  function studentInfo(u) {
    var st = statusOf(DB.rows('answers').filter(function (r) { return String(r.userId) === String(u.id); }));
    return { id: String(u.id), name: String(u.name), class: String(u.class), username: String(u.username),
      didPre: st.didPre, didPost: st.didPost, weak: st.weak, postOpen: setting('post:' + norm(u.class)) === 'yes' };
  }
  function pubStudent(u) { return { id: String(u.id), name: String(u.name), class: String(u.class), username: String(u.username), key: String(u.key || ''), active: isActive(u), lastLogin: iso(u.lastLogin) }; }
  function pubStaff(u) { return { id: String(u.id), name: String(u.name), role: String(u.role), username: String(u.username), classes: String(u.classes || ''), active: isActive(u), lastLogin: iso(u.lastLogin) }; }
  function newUser(role, o) {
    var salt = rid(16), pw = String(o.password || '') || genPw();
    return { password: pw, rec: { id: (role === 'student' ? 'S' : role === 'teacher' ? 'T' : 'A') + rid(10), role: role, username: o.username,
      name: o.name || '', class: o.class || '', classes: o.classes || '', salt: salt, hash: hashPw(pw, salt),
      key: role === 'student' ? rid(12) : '', active: 'yes', created: DB.now(), lastLogin: '' } };
  }
  function scopedStudents(s) {
    var me = byId(s.id), mine = myClasses(me), mineN = mine ? mine.map(norm) : null;
    return users().filter(function (u) { return u.role === 'student' && (!mineN || mineN.indexOf(norm(u.class)) >= 0); });
  }

  var A = {};
  A._setup = function () {
    if (!users().some(function (u) { return u.role === 'admin'; }))
      DB.insert('users', newUser('admin', { username: 'admin', name: 'مدير النظام', password: 'admin1234' }).rec);
  };
  A.login = function (username, password) {
    var un = cleanUser(username), g = guard('u_' + un);
    var u = users().find(function (x) { return norm(x.username) === un; });
    if (!u || !isActive(u) || hashPw(password, u.salt) !== String(u.hash)) { g.fail(); throw err('BAD_LOGIN'); }
    return { token: startSession(u), role: String(u.role), user: u.role === 'student' ? studentInfo(u) : pubStaff(u) };
  };
  A.loginKey = function (key) {
    key = String(key || ''); if (key.length < 8) throw err('BAD_KEY');
    var u = users().find(function (x) { return x.role === 'student' && String(x.key) === key; });
    if (!u || !isActive(u)) throw err('BAD_KEY');
    return { token: startSession(u), role: 'student', user: studentInfo(u) };
  };
  A.characters = function (token) {
    sess(token);
    return DB.rows('characters').map(function (c) { return { id: String(c.id), name: String(c.name), img: String(c.img) }; });
  };
  A.logAnswers = function (token, list) {
    var s = sess(token, ['student']);
    if (!Array.isArray(list) || !list.length) return true;
    var now = DB.now();
    var rows = list.slice(0, 500).map(function (x) { return { time: now, userId: s.id, mode: String(x.mode), qid: String(x.qid || '').slice(0, 90),
      subject: String(x.s || ''), domain: String(x.d || ''), skill: String(x.k || ''), correct: x.ok ? 1 : 0, ms: Number(x.ms) || 0 }; });
    DB.lock(function () { DB.insertMany('answers', rows); });
    return true;
  };
  A.changePassword = function (token, oldPw, newPw) {
    var s = sess(token), u = byId(s.id);
    if (hashPw(oldPw, u.salt) !== String(u.hash)) throw err('BAD_LOGIN');
    if (String(newPw).length < 4) throw err('SHORT');
    var salt = rid(16); DB.update('users', 'id', u.id, { salt: salt, hash: hashPw(newPw, salt) });
    return true;
  };
  A.dashboard = function (token) {
    var s = sess(token, ['admin', 'teacher']), me = byId(s.id), all = users(), mine = myClasses(me);
    var studs = scopedStudents(s), ids = {};
    studs.forEach(function (u) { ids[String(u.id)] = 1; });
    var ans = DB.rows('answers').filter(function (a) { return ids[String(a.userId)]; })
      .map(function (a) { return { studentId: a.userId, mode: a.mode, domain: a.domain, skill: a.skill, correct: a.correct, time: a.time }; });
    var cl = mine ? mine.slice() : studs.map(function (u) { return String(u.class).trim(); })
      .concat(all.filter(function (u) { return u.role === 'teacher'; }).reduce(function (a, t) { return a.concat(String(t.classes || '').split(',')); }, []));
    var seen = {}, classes = [];
    cl.map(function (x) { return String(x).trim(); }).filter(Boolean).forEach(function (c) { if (!seen[norm(c)]) { seen[norm(c)] = 1; classes.push(c); } });
    var post = {}; classes.forEach(function (c) { post[c] = setting('post:' + norm(c)) === 'yes'; });
    return { appUrl: DB.appUrl ? DB.appUrl() : '', me: pubStaff(me), classes: classes.sort(), students: studs.map(pubStudent), agg: aggregate(ans), post: post,
      characters: DB.rows('characters').map(function (c) { return { id: String(c.id), name: String(c.name), img: String(c.img) }; }),
      teachers: s.role === 'admin' ? all.filter(function (u) { return u.role !== 'student'; }).map(pubStaff) : [] };
  };
  A.addStudents = function (token, cls, list) {
    var s = sess(token, ['admin', 'teacher']); cls = String(cls || '').trim();
    if (!cls) throw err('NO_CLASS'); if (!canClass(s, cls)) throw err('FORBIDDEN');
    return DB.lock(function () {
      var all = users(), taken = {}, out = [], recs = [];
      all.forEach(function (u) { taken[norm(u.username)] = 1; });
      var base = norm(cls).replace(/[^a-z0-9]/g, '') || 'st';
      var n = all.filter(function (u) { return u.role === 'student' && norm(u.class) === norm(cls); }).length;
      (list || []).forEach(function (it) {
        var name = String(it.name || '').trim().slice(0, 40); if (!name) return;
        var un = cleanUser(it.username || '');
        if (!un || un.length < 3 || taken[un]) { do { n++; un = base + '-' + (n < 10 ? '0' : '') + n; } while (taken[un]); }
        taken[un] = 1;
        var r = newUser('student', { username: un, name: name, class: cls, password: String(it.password || '').trim() });
        recs.push(r.rec); out.push({ id: r.rec.id, name: name, class: cls, username: un, password: r.password, key: r.rec.key });
      });
      DB.insertMany('users', recs);
      return out;
    });
  };
  A.updateStudent = function (token, id, p) {
    var s = sess(token, ['admin', 'teacher']), u = byId(id);
    if (!u || u.role !== 'student') throw err('NOT_FOUND'); if (!canClass(s, u.class)) throw err('FORBIDDEN');
    var patch = {};
    if (p.name != null) patch.name = String(p.name).trim().slice(0, 40);
    if (p.username != null) { var un = cleanUser(p.username); if (un.length < 3) throw err('SHORT'); if (!usernameFree(un, id)) throw err('EXISTS'); patch.username = un; }
    if (p.class != null && norm(p.class) !== norm(u.class)) { if (!canClass(s, p.class)) throw err('FORBIDDEN'); patch.class = String(p.class).trim(); }
    if (p.active != null) patch.active = p.active ? 'yes' : 'no';
    DB.update('users', 'id', id, patch);
    return pubStudent(Object.assign({}, u, patch));
  };
  A.resetPassword = function (token, id) {
    var s = sess(token, ['admin', 'teacher']), u = byId(id);
    if (!u) throw err('NOT_FOUND');
    if (u.role === 'student') { if (!canClass(s, u.class)) throw err('FORBIDDEN'); }
    else if (!(s.role === 'admin' && u.role === 'teacher')) throw err('FORBIDDEN');
    var pw = u.role === 'student' ? genPw() : rid(6), salt = rid(16), patch = { salt: salt, hash: hashPw(pw, salt) };
    if (u.role === 'student') patch.key = rid(12);
    DB.update('users', 'id', id, patch);
    return { id: String(u.id), password: pw, key: patch.key || '', username: String(u.username), name: String(u.name), class: String(u.class) };
  };
  A.addTeacher = function (token, o) {
    sess(token, ['admin']);
    var un = cleanUser(o.username); if (un.length < 3) throw err('SHORT'); if (!usernameFree(un)) throw err('EXISTS');
    var r = newUser('teacher', { username: un, name: String(o.name || '').trim(), classes: cleanClasses(o.classes), password: String(o.password || '').trim() || rid(6) });
    DB.insert('users', r.rec);
    var out = pubStaff(r.rec); out.password = r.password; return out;
  };
  A.updateTeacher = function (token, id, p) {
    sess(token, ['admin']); var u = byId(id);
    if (!u || u.role !== 'teacher') throw err('NOT_FOUND');
    var patch = {};
    if (p.name != null) patch.name = String(p.name).trim();
    if (p.classes != null) patch.classes = cleanClasses(p.classes);
    if (p.username != null) { var un = cleanUser(p.username); if (un.length < 3) throw err('SHORT'); if (!usernameFree(un, id)) throw err('EXISTS'); patch.username = un; }
    if (p.active != null) patch.active = p.active ? 'yes' : 'no';
    DB.update('users', 'id', id, patch);
    return pubStaff(Object.assign({}, u, patch));
  };
  A.setPostOpen = function (token, cls, open) {
    var s = sess(token, ['admin', 'teacher']); if (!canClass(s, cls)) throw err('FORBIDDEN');
    setSetting('post:' + norm(cls), open ? 'yes' : 'no'); return true;
  };
  A.saveCharacter = function (token, name, img) {
    sess(token, ['admin']); if (String(img).length > 49000) throw err('TOO_BIG');
    var c = { id: 'C' + rid(8), name: String(name).slice(0, 30), img: String(img) };
    DB.insert('characters', c); return c;
  };
  A.deleteCharacter = function (token, id) { sess(token, ['admin']); DB.remove('characters', 'id', id); return true; };
  A.exportAnswers = function (token) {
    var s = sess(token, ['admin', 'teacher']), studs = scopedStudents(s), map = {};
    studs.forEach(function (u) { map[String(u.id)] = u; });
    return DB.rows('answers').filter(function (a) { return map[String(a.userId)]; }).map(function (a) {
      var u = map[String(a.userId)];
      return { time: iso(a.time), name: String(u.name), username: String(u.username), class: String(u.class), mode: a.mode, qid: a.qid,
        subject: a.subject, domain: a.domain, skill: a.skill, correct: Number(a.correct), ms: Number(a.ms) };
    });
  };
  return A;
}
/* ================= Google Sheets ================= */
function sh_(t) {
  var ss = SpreadsheetApp.getActive(), sh = ss.getSheetByName(t);
  if (!sh) { sh = ss.insertSheet(t); sh.appendRow(TABLES[t]); sh.setFrozenRows(1); }
  return sh;
}
function prep_(v) { return (typeof v === 'string' && v !== '') ? "'" + v : v; }
var DB = {
  rows: function (t) {
    var v = sh_(t).getDataRange().getValues(), h = v.shift();
    return v.filter(function (r) { return r[0] !== ''; }).map(function (r) { var o = {}; h.forEach(function (k, i) { o[k] = r[i]; }); return o; });
  },
  insertMany: function (t, arr) {
    if (!arr.length) return;
    var sh = sh_(t), h = TABLES[t];
    var vals = arr.map(function (o) { return h.map(function (k) { return prep_(o[k] == null ? '' : o[k]); }); });
    sh.getRange(sh.getLastRow() + 1, 1, vals.length, h.length).setValues(vals);
  },
  insert: function (t, o) { DB.insertMany(t, [o]); },
  update: function (t, kf, kv, patch) {
    var sh = sh_(t), v = sh.getDataRange().getValues(), h = v[0], ki = h.indexOf(kf);
    for (var i = 1; i < v.length; i++) if (String(v[i][ki]) === String(kv)) {
      Object.keys(patch).forEach(function (k) { var c = h.indexOf(k); if (c >= 0) sh.getRange(i + 1, c + 1).setValue(prep_(patch[k])); });
      return true;
    }
    return false;
  },
  remove: function (t, kf, kv) {
    var sh = sh_(t), v = sh.getDataRange().getValues(), ki = v[0].indexOf(kf);
    for (var i = v.length - 1; i >= 1; i--) if (String(v[i][ki]) === String(kv)) sh.deleteRow(i + 1);
  },
  uuid: function () { return Utilities.getUuid(); },
  cacheGet: function (k) { return CacheService.getScriptCache().get(k); },
  cachePut: function (k, v, s) { CacheService.getScriptCache().put(k, v, s); },
  lock: function (fn) { var l = LockService.getScriptLock(); l.waitLock(20000); try { return fn(); } finally { l.releaseLock(); } },
  now: function () { return new Date(); },
  appUrl: function () { try { return ScriptApp.getService().getUrl() || ''; } catch (e) { return ''; } }
};
var API = makeAPI(DB);

/* ================= نقاط الدخول ================= */
function doGet() {
  return HtmlService.createHtmlOutputFromFile('Index')
    .setTitle('جزيرة التحدي')
    .addMetaTag('viewport', 'width=device-width, initial-scale=1')
    .setXFrameOptionsMode(HtmlService.XFrameOptionsMode.ALLOWALL);
}
/** للنسخة المنشورة على Apps Script */
function run(fn, args) {
  if (!API[fn] || fn.charAt(0) === '_') throw new Error('UNKNOWN');
  return API[fn].apply(null, args || []);
}
/** للنسخة المنشورة على GitHub Pages */
function doPost(e) {
  var out;
  try { var req = JSON.parse(e.postData.contents); out = { result: run(req.fn, req.args) }; }
  catch (err) { out = { error: String((err && err.message) || err) }; }
  return ContentService.createTextOutput(JSON.stringify(out)).setMimeType(ContentService.MimeType.JSON);
}
/** يُشغَّل مرة واحدة من المحرر: ينشئ الأوراق وحساب المدير (admin / admin1234) */
function setup() {
  Object.keys(TABLES).forEach(sh_);
  API._setup();
}
