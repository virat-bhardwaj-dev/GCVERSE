import { initializeApp } from "https://www.gstatic.com/firebasejs/11.10.0/firebase-app.js";
import { getAnalytics, isSupported as analyticsIsSupported } from "https://www.gstatic.com/firebasejs/11.10.0/firebase-analytics.js";
import {
  getAuth, onAuthStateChanged, createUserWithEmailAndPassword,
  signInWithEmailAndPassword, GoogleAuthProvider, signInWithPopup,
  signOut, updateProfile
} from "https://www.gstatic.com/firebasejs/11.10.0/firebase-auth.js";
import {
  getFirestore, collection, doc, getDoc, getDocs, query, where,
  onSnapshot, runTransaction, writeBatch, Timestamp
} from "https://www.gstatic.com/firebasejs/11.10.0/firebase-firestore.js";

const firebaseConfig = {
  apiKey: "AIzaSyB5n2L0mKUKxcwlUYa_BW_tR-x98G2zxbY",
  authDomain: "gcverse-3b48c.firebaseapp.com",
  projectId: "gcverse-3b48c",
  storageBucket: "gcverse-3b48c.firebasestorage.app",
  messagingSenderId: "214074252875",
  appId: "1:214074252875:web:fbcc066a4155b99e3cb7ce",
  measurementId: "G-ZZ2P462BXN"
};

const firebaseApp = initializeApp(firebaseConfig);
const firebaseAuth = getAuth(firebaseApp);
const cloudStore = getFirestore(firebaseApp);
analyticsIsSupported().then(supported => { if (supported) getAnalytics(firebaseApp); }).catch(() => {});

(() => {
  'use strict';

  const DB_KEY = 'gcverse_v1_demo_db';
  const SESSION_KEY = 'gcverse_v1_demo_session';
  const PROJECT_LINKS = {
    studyflow: 'https://studyflow-student18.vercel.app/', 
    spendnest: 'https://spendnest-five.vercel.app/'  
  };

  const $ = (selector, root = document) => root.querySelector(selector);
  const $$ = (selector, root = document) => Array.from(root.querySelectorAll(selector));
  const now = () => Date.now();
  const uid = (prefix = 'id') => `${prefix}_${Math.random().toString(36).slice(2, 8)}${Date.now().toString(36).slice(-4)}`;
  const escapeHtml = (value = '') => String(value).replace(/[&<>"']/g, char => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[char]));
  const initials = (name = '?') => name.trim().split(/\s+/).slice(0, 2).map(part => part[0] || '').join('').toUpperCase() || '?';
  const formatDate = value => new Date(value).toLocaleDateString(undefined, { month: 'short', day: 'numeric' });
  const ago = value => {
    const seconds = Math.max(0, Math.floor((now() - value) / 1000));
    if (seconds < 60) return 'just now';
    if (seconds < 3600) return `${Math.floor(seconds / 60)}m ago`;
    if (seconds < 86400) return `${Math.floor(seconds / 3600)}h ago`;
    return `${Math.floor(seconds / 86400)}d ago`;
  };
  const remaining = value => {
    const ms = Math.max(0, value - now());
    const hours = Math.floor(ms / 3600000);
    const minutes = Math.floor((ms % 3600000) / 60000);
    return hours > 0 ? `${hours}h ${minutes}m left` : `${minutes}m left`;
  };
  const random = max => Math.floor(Math.random() * max);
  const shuffle = items => [...items].sort(() => Math.random() - 0.5);
  const pick = items => items[random(items.length)];
  const safeParse = (value, fallback) => { try { return JSON.parse(value) ?? fallback; } catch { return fallback; } };
  const normalizeUsername = value => String(value || '').toLowerCase().trim().replace(/^@+/, '').replace(/[^a-z0-9._]/g, '').replace(/\.{2,}/g, '.').replace(/_{2,}/g, '_').slice(0, 20);

  const blankDb = () => ({ users: {}, gcs: [], confessions: [], stats: {}, gcStats: {}, gameSessions: [], userPrefs: {}, messages: [], coupleRooms: [] });
  let db = safeParse(localStorage.getItem(DB_KEY), blankDb());
  db.users ||= {}; db.gcs ||= []; db.confessions ||= []; db.stats ||= {}; db.gcStats ||= {}; db.gameSessions ||= []; db.userPrefs ||= {}; db.messages ||= []; db.coupleRooms ||= [];
  let currentUserId = '';
  let page = 'home';
  let selectedGcId = '';
  let confessionScope = 'gcs';
  let confessionGcFilter = 'all';
  let toastTimer = null;
  let game = null;
  let mobileNavOpen = false;
  let chatTargetType = 'gc';
  let chatTargetId = '';
  let activeCoupleRoomId = '';

  // Firebase state: localStorage is not used as the source of truth after sign-in.
  let cloudReady = false;
  let applyingRemoteSnapshot = false;
  let cloudSyncTimer = null;
  let cloudSyncRunning = false;
  let cloudSyncQueued = false;
  let pendingDisplayName = '';
  let authStateRun = 0;
  const cloudBaseline = new Map();
  const baseUnsubscribers = [];
  const confessionUnsubscribers = new Map();
  const privateConfessionOwnerIds = new Set();
  let lastCloudErrorAt = 0;

  function stableValue(value) {
    if (value instanceof Timestamp) return { $timestamp: value.toMillis() };
    if (value && typeof value.toMillis === 'function') {
      try { return { $timestamp: value.toMillis() }; } catch {}
    }
    if (Array.isArray(value)) return value.map(stableValue);
    if (value && typeof value === 'object') {
      const result = {};
      Object.keys(value).sort().forEach(key => {
        if (value[key] !== undefined) result[key] = stableValue(value[key]);
      });
      return result;
    }
    return value;
  }
  function stableStringify(value) { return JSON.stringify(stableValue(value)); }
  function cloudKey(path, id) { return `${path}/${id}`; }
  function addCloudEntry(entries, path, id, data) {
    if (!id || !data) return;
    entries.set(cloudKey(path, id), { path, id: String(id), data });
  }
  function ttlField(expiresAt) {
    return Number.isFinite(Number(expiresAt)) ? Timestamp.fromMillis(Number(expiresAt)) : null;
  }
  function buildCloudEntries() {
    const entries = new Map();
    Object.values(db.users || {}).forEach(user => {
      if (!user?.id || String(user.id).startsWith('preview_')) return;
      addCloudEntry(entries, 'users', user.id, {
        id: user.id, name: String(user.name || 'Player').slice(0, 24),
        username: normalizeUsername(user.username || '') || 'player',
        avatar: user.avatar || initials(user.name || 'Player'),
        createdAt: Number(user.createdAt || now())
      });
    });
    Object.entries(db.stats || {}).forEach(([id, value]) => {
      if (!id || id.startsWith('preview_')) return;
      addCloudEntry(entries, 'stats', id, { id, xp: Number(value.xp || 0), gamesPlayed: Number(value.gamesPlayed || 0), wins: Number(value.wins || 0), streak: Number(value.streak || 0), bestPuzzle: Number(value.bestPuzzle || 0) });
    });
    if (currentUserId && db.userPrefs?.[currentUserId]) {
      addCloudEntry(entries, 'userPrefs', currentUserId, { id: currentUserId, ...db.userPrefs[currentUserId] });
    }
    (db.gcs || []).forEach(gc => {
      if (!gc?.id || !gc.ownerId) return;
      const memberIds = [...new Set((gc.members || []).filter(member => member.userId && !member.preview && !String(member.userId).startsWith('preview_')).map(member => member.userId))];
      const normalized = { ...gc, id: gc.id, memberIds, members: (gc.members || []).map(member => ({ ...member })) };
      addCloudEntry(entries, 'gcs', gc.id, normalized);
      // Invite codes are a get-only lookup; owners create them alongside the GC.
      if (gc.ownerId === currentUserId && gc.inviteCode) addCloudEntry(entries, 'gcInvites', String(gc.inviteCode).toUpperCase(), { id: String(gc.inviteCode).toUpperCase(), gcId: gc.id, ownerId: gc.ownerId });
    });
    (db.confessions || []).forEach(item => {
      if (!item?.id) return;
      const gc = item.scope === 'gc' ? db.gcs.find(group => group.id === item.gcId) : null;
      // Keep anonymous identity out of the public confession document entirely.
      const payload = { ...item, id: item.id, authorId: item.anonymous ? null : item.authorId, authorName: item.anonymous ? 'Anonymous' : item.authorName, ttlAt: ttlField(item.expiresAt) };
      if (item.scope === 'gc') payload.memberIds = item.memberIds || (gc?.members || []).filter(member => !member.preview).map(member => member.userId);
      addCloudEntry(entries, 'confessions', item.id, payload);
      if (item.anonymous && (item.authorId === currentUserId || privateConfessionOwnerIds.has(item.id))) {
        privateConfessionOwnerIds.add(item.id);
        addCloudEntry(entries, 'confessionOwners', item.id, { id: item.id, postId: item.id, authorId: currentUserId, createdAt: Number(item.createdAt || now()), expiresAt: Number(item.expiresAt || now() + 86400000), ttlAt: ttlField(item.expiresAt) });
      }
    });
    (db.messages || []).forEach(message => {
      if (!message?.id || !message.fromId) return;
      const gc = message.type === 'gc' ? db.gcs.find(group => group.id === message.gcId) : null;
      const memberIds = message.memberIds || (message.type === 'gc'
        ? [...new Set((gc?.members || []).filter(member => !member.preview).map(member => member.userId))]
        : [...new Set([message.fromId, message.toId].filter(Boolean))]);
      addCloudEntry(entries, 'messages', message.id, { ...message, id: message.id, memberIds, ttlAt: ttlField(message.expiresAt) });
    });
    (db.coupleRooms || []).forEach(room => {
      if (!room?.id || !room.ownerId) return;
      const memberIds = [...new Set([room.ownerId, room.partnerId].filter(Boolean))];
      const roomPayload = { ...room, id: room.id, memberIds, answeredBy: room.answeredBy || {}, ttlAt: ttlField(room.expiresAt) };
      // Answers live in individual documents; Firestore rules only let the owner read theirs
      // until both room members have submitted that round.
      delete roomPayload.responses;
      delete roomPayload.answerCreatedAt;
      addCloudEntry(entries, 'coupleRooms', room.id, roomPayload);
      Object.entries(room.responses || {}).forEach(([roundIndex, roundResponses]) => {
        const answer = roundResponses?.[currentUserId];
        if (answer === undefined || !memberIds.includes(currentUserId)) return;
        const answerId = `${room.id}_${roundIndex}_${currentUserId}`;
        addCloudEntry(entries, 'coupleAnswers', answerId, { id: answerId, roomId: room.id, roundKey: String(roundIndex), index: Number(roundIndex), userId: currentUserId, answer: String(answer), memberIds, createdAt: Number(room.answerCreatedAt?.[roundIndex]?.[currentUserId] || room.createdAt || now()), expiresAt: Number(room.expiresAt || now() + 86400000), ttlAt: ttlField(room.expiresAt) });
      });
      if (room.ownerId === currentUserId && room.code) addCloudEntry(entries, 'coupleRoomCodes', String(room.code).toUpperCase(), { id: String(room.code).toUpperCase(), roomId: room.id, ownerId: room.ownerId, ttlAt: ttlField(room.expiresAt) });
    });
    (db.gameSessions || []).forEach(session => {
      if (!session?.id || !session.userId) return;
      addCloudEntry(entries, 'gameSessions', session.id, { ...session, id: session.id, userIds: [session.userId], ttlAt: ttlField(session.expiresAt) });
    });
    return entries;
  }
  function trackSnapshot(path, docs) {
    docs.forEach(snapshot => cloudBaseline.set(cloudKey(path, snapshot.id), stableStringify(snapshot.data())));
  }
  function stripSystemFields(data) {
    const copy = { ...data };
    delete copy.ttlAt;
    return copy;
  }
  function readCloudDoc(snapshot) {
    return { ...stripSystemFields(snapshot.data()), id: snapshot.data().id || snapshot.id };
  }
  function stopCloudListeners() {
    baseUnsubscribers.splice(0).forEach(unsubscribe => { try { unsubscribe(); } catch {} });
    confessionUnsubscribers.forEach(unsubscribe => { try { unsubscribe(); } catch {} });
    confessionUnsubscribers.clear();
  }
  function announceCloudError(error, context = 'Firebase') {
    const stamp = Date.now();
    if (stamp - lastCloudErrorAt < 2500) return;
    lastCloudErrorAt = stamp;
    console.error(`${context} error:`, error);
    toast(error?.code === 'permission-denied'
      ? 'Firestore denied this action. Check that firestore.rules are published.'
      : `${context} failed. Check Firebase setup and internet connection.`, 'error');
  }
  function refreshAfterCloudChange() {
    if (!cloudReady || !currentUser()) return;
    cleanExpired();
    renderSidebar();
    renderPage();
    refreshIcons();
  }
  function applyRemoteCollection(path, snapshot, transform) {
    applyingRemoteSnapshot = true;
    try {
      trackSnapshot(path, snapshot.docs);
      transform(snapshot.docs.map(readCloudDoc));
      refreshAfterCloudChange();
    } finally {
      applyingRemoteSnapshot = false;
      persist();
    }
  }
  function applyConfessionsSnapshot(snapshot, groupId = '') {
    applyingRemoteSnapshot = true;
    try {
      trackSnapshot('confessions', snapshot.docs);
      const docs = snapshot.docs.map(readCloudDoc);
      if (!groupId) {
        db.confessions = [...db.confessions.filter(item => item.scope !== 'global'), ...docs];
      } else {
        db.confessions = [...db.confessions.filter(item => item.gcId !== groupId), ...docs];
      }
      db.confessions = [...new Map(db.confessions.map(item => [item.id, item])).values()];
      refreshAfterCloudChange();
    } finally {
      applyingRemoteSnapshot = false;
      persist();
    }
  }
  function syncGroupConfessionListeners(groups) {
    const ids = new Set(groups.map(group => group.id));
    for (const [id, unsubscribe] of confessionUnsubscribers.entries()) {
      if (!ids.has(id)) { unsubscribe(); confessionUnsubscribers.delete(id); }
    }
    groups.forEach(group => {
      if (confessionUnsubscribers.has(group.id)) return;
      const q = query(collection(cloudStore, 'confessions'), where('gcId', '==', group.id));
      const unsubscribe = onSnapshot(q, snapshot => applyConfessionsSnapshot(snapshot, group.id), error => announceCloudError(error, 'GC confessions sync'));
      confessionUnsubscribers.set(group.id, unsubscribe);
    });
  }
  async function hydrateCoupleRoomResponses(room) {
    if (!room?.id || !currentUserId) return;
    room.responses ||= {};
    const roundKey = String(room.index || 0);
    room.responses[roundKey] ||= {};
    const memberIds = [...new Set([room.ownerId, room.partnerId].filter(Boolean))];
    if (!memberIds.includes(currentUserId)) return;
    const answeredBy = room.answeredBy?.[roundKey] || [];
    const canRevealBoth = memberIds.length === 2 && memberIds.every(id => answeredBy.includes(id));
    const readableIds = canRevealBoth ? memberIds : [currentUserId];
    const snapshots = await Promise.all(readableIds.map(userId => getDoc(doc(cloudStore, 'coupleAnswers', `${room.id}_${roundKey}_${userId}`)).catch(() => null)));
    snapshots.forEach((snapshot, index) => {
      if (!snapshot?.exists()) return;
      cloudBaseline.set(cloudKey('coupleAnswers', snapshot.id), stableStringify(snapshot.data()));
      const data = snapshot.data();
      const answerUserId = data.userId || readableIds[index];
      room.responses[roundKey][answerUserId] = data.answer;
      room.answerCreatedAt ||= {};
      room.answerCreatedAt[roundKey] ||= {};
      room.answerCreatedAt[roundKey][answerUserId] = Number(data.createdAt || room.createdAt || now());
    });
    if (!canRevealBoth) {
      // Keep only our own answer in local memory before the other player has answered.
      Object.keys(room.responses[roundKey]).forEach(id => { if (id !== currentUserId) delete room.responses[roundKey][id]; });
    }
    const idx = db.coupleRooms.findIndex(item => item.id === room.id);
    if (idx >= 0) db.coupleRooms[idx] = room;
    if (page === 'couples' && activeCoupleRoomId === room.id) { renderPage(); refreshIcons(); }
  }
  function hydrateCoupleRooms(rooms) {
    rooms.forEach(room => { void hydrateCoupleRoomResponses(room).catch(() => {}); });
  }

  async function loadCloudData(user) {
    const uid = user.uid;
    cloudReady = false;
    const [usersSnap, statsSnap, groupsSnap, globalConfessionsSnap, messagesSnap, roomsSnap, sessionsSnap, ownAnswersSnap, privateConfessionOwnersSnap, prefsSnap] = await Promise.all([
      getDocs(collection(cloudStore, 'users')),
      getDocs(collection(cloudStore, 'stats')),
      getDocs(query(collection(cloudStore, 'gcs'), where('memberIds', 'array-contains', uid))),
      getDocs(query(collection(cloudStore, 'confessions'), where('scope', '==', 'global'))),
      getDocs(query(collection(cloudStore, 'messages'), where('memberIds', 'array-contains', uid))),
      getDocs(query(collection(cloudStore, 'coupleRooms'), where('memberIds', 'array-contains', uid))),
      getDocs(query(collection(cloudStore, 'gameSessions'), where('userIds', 'array-contains', uid))),
      getDocs(query(collection(cloudStore, 'coupleAnswers'), where('userId', '==', uid))),
      getDocs(query(collection(cloudStore, 'confessionOwners'), where('authorId', '==', uid))),
      getDoc(doc(cloudStore, 'userPrefs', uid))
    ]);
    const groups = groupsSnap.docs.map(readCloudDoc);
    const groupConfessionSnaps = await Promise.all(groups.map(group => getDocs(query(collection(cloudStore, 'confessions'), where('gcId', '==', group.id)))));
    db = blankDb();
    trackSnapshot('users', usersSnap.docs);
    usersSnap.docs.forEach(snapshot => {
      const userData = readCloudDoc(snapshot);
      db.users[userData.id] = userData;
    });
    if (db.users[uid]) db.users[uid].email = user.email || '';
    trackSnapshot('stats', statsSnap.docs);
    statsSnap.docs.forEach(snapshot => { const data = readCloudDoc(snapshot); delete data.id; db.stats[snapshot.id] = data; });
    trackSnapshot('gcs', groupsSnap.docs);
    db.gcs = groups;
    trackSnapshot('confessions', globalConfessionsSnap.docs);
    db.confessions = globalConfessionsSnap.docs.map(readCloudDoc);
    groupConfessionSnaps.forEach(snapshot => {
      trackSnapshot('confessions', snapshot.docs);
      db.confessions.push(...snapshot.docs.map(readCloudDoc));
    });
    db.confessions = [...new Map(db.confessions.map(item => [item.id, item])).values()];
    trackSnapshot('messages', messagesSnap.docs); db.messages = messagesSnap.docs.map(readCloudDoc);
    trackSnapshot('coupleRooms', roomsSnap.docs); db.coupleRooms = roomsSnap.docs.map(readCloudDoc).map(room => ({ ...room, responses: {} }));
    trackSnapshot('gameSessions', sessionsSnap.docs); db.gameSessions = sessionsSnap.docs.map(readCloudDoc);
    trackSnapshot('coupleAnswers', ownAnswersSnap.docs);
    privateConfessionOwnerIds.clear();
    trackSnapshot('confessionOwners', privateConfessionOwnersSnap.docs);
    privateConfessionOwnersSnap.docs.forEach(snapshot => privateConfessionOwnerIds.add(snapshot.id));
    ownAnswersSnap.docs.forEach(snapshot => { const answer = readCloudDoc(snapshot); const room = db.coupleRooms.find(item => item.id === answer.roomId); if (room) { room.responses ||= {}; room.responses[String(answer.roundKey)] ||= {}; room.responses[String(answer.roundKey)][answer.userId] = answer.answer; room.answerCreatedAt ||= {}; room.answerCreatedAt[String(answer.roundKey)] ||= {}; room.answerCreatedAt[String(answer.roundKey)][answer.userId] = Number(answer.createdAt || room.createdAt || now()); } });
    if (prefsSnap.exists()) { trackSnapshot('userPrefs', [prefsSnap]); const prefs = readCloudDoc(prefsSnap); delete prefs.id; db.userPrefs[uid] = prefs; }
    else db.userPrefs[uid] = {};
    db.users[uid] ||= { id: uid, name: user.displayName || 'Player', username: createUniqueUsername(user.displayName || 'player', uid), email: user.email || '', avatar: initials(user.displayName || 'Player'), createdAt: now() };
    db.users[uid].email = user.email || '';
    statsFor(uid);
    cloudReady = true;
    syncGroupConfessionListeners(db.gcs);
    hydrateCoupleRooms(db.coupleRooms);
    persist();
    startRealtimeListeners(user);
    cleanExpired();
  }
  function startRealtimeListeners(user) {
    const uid = user.uid;
    baseUnsubscribers.push(onSnapshot(collection(cloudStore, 'users'), snapshot => {
      applyRemoteCollection('users', snapshot, docs => {
        const next = {};
        docs.forEach(data => { next[data.id] = data; });
        if (next[uid]) next[uid].email = firebaseAuth.currentUser?.email || '';
        db.users = next;
        db.users[uid] ||= { id: uid, name: user.displayName || 'Player', username: 'player', email: user.email || '', avatar: initials(user.displayName || 'Player'), createdAt: now() };
      });
    }, error => announceCloudError(error, 'Profile sync')));
    baseUnsubscribers.push(onSnapshot(collection(cloudStore, 'stats'), snapshot => applyRemoteCollection('stats', snapshot, docs => {
      const next = {}; docs.forEach(data => { const id = data.id; delete data.id; next[id] = data; }); db.stats = next; statsFor(uid);
    }), error => announceCloudError(error, 'Leaderboard sync')));
    baseUnsubscribers.push(onSnapshot(query(collection(cloudStore, 'gcs'), where('memberIds', 'array-contains', uid)), snapshot => {
      applyRemoteCollection('gcs', snapshot, docs => { db.gcs = docs; syncGroupConfessionListeners(docs); });
    }, error => announceCloudError(error, 'GC sync')));
    baseUnsubscribers.push(onSnapshot(query(collection(cloudStore, 'confessions'), where('scope', '==', 'global')), snapshot => applyConfessionsSnapshot(snapshot), error => announceCloudError(error, 'Confessions sync')));
    baseUnsubscribers.push(onSnapshot(query(collection(cloudStore, 'messages'), where('memberIds', 'array-contains', uid)), snapshot => applyRemoteCollection('messages', snapshot, docs => { db.messages = docs; }), error => announceCloudError(error, 'Messages sync')));
    baseUnsubscribers.push(onSnapshot(query(collection(cloudStore, 'coupleRooms'), where('memberIds', 'array-contains', uid)), snapshot => applyRemoteCollection('coupleRooms', snapshot, docs => { const previous = new Map(db.coupleRooms.map(room => [room.id, room])); db.coupleRooms = docs.map(room => { const old = previous.get(room.id); return { ...room, responses: old?.responses || {}, answerCreatedAt: old?.answerCreatedAt || {} }; }); hydrateCoupleRooms(db.coupleRooms); }), error => announceCloudError(error, 'Couples rooms sync')));
    baseUnsubscribers.push(onSnapshot(query(collection(cloudStore, 'gameSessions'), where('userIds', 'array-contains', uid)), snapshot => applyRemoteCollection('gameSessions', snapshot, docs => { db.gameSessions = docs; }), error => announceCloudError(error, 'Game history sync')));
    baseUnsubscribers.push(onSnapshot(doc(cloudStore, 'userPrefs', uid), snapshot => {
      if (!snapshot.exists()) return;
      applyingRemoteSnapshot = true;
      try { cloudBaseline.set(cloudKey('userPrefs', uid), stableStringify(snapshot.data())); const prefs = readCloudDoc(snapshot); delete prefs.id; db.userPrefs[uid] = prefs; refreshAfterCloudChange(); }
      finally { applyingRemoteSnapshot = false; persist(); }
    }, error => announceCloudError(error, 'Preferences sync')));
  }
  async function ensureCloudProfile(user, requestedName = '') {
    const userRef = doc(cloudStore, 'users', user.uid);
    const existing = await getDoc(userRef);
    if (existing.exists()) return readCloudDoc(existing);
    const displayName = String(requestedName || user.displayName || user.email?.split('@')[0] || 'Player').trim().slice(0, 24) || 'Player';
    const rawBase = normalizeUsername(displayName.replace(/\s+/g, '.')) || 'player';
    const base = rawBase.length >= 3 ? rawBase : `${rawBase}player`.slice(0, 20);
    for (let index = 1; index < 1000; index += 1) {
      const username = index === 1 ? base : `${base.slice(0, Math.max(3, 20 - String(index).length))}${index}`;
      const usernameRef = doc(cloudStore, 'usernames', username);
      const statsRef = doc(cloudStore, 'stats', user.uid);
      const prefsRef = doc(cloudStore, 'userPrefs', user.uid);
      const outcome = await runTransaction(cloudStore, async transaction => {
        const [userSnap, usernameSnap, statsSnap, prefsSnap] = await Promise.all([
          transaction.get(userRef), transaction.get(usernameRef), transaction.get(statsRef), transaction.get(prefsRef)
        ]);
        if (userSnap.exists()) return { exists: true, profile: userSnap.data() };
        if (usernameSnap.exists() && usernameSnap.data().userId !== user.uid) return { conflict: true };
        const profile = { id: user.uid, name: displayName, username, avatar: initials(displayName), createdAt: now() };
        transaction.set(usernameRef, { id: username, userId: user.uid, createdAt: now() });
        transaction.set(userRef, profile);
        if (!statsSnap.exists()) transaction.set(statsRef, { id: user.uid, xp: 0, gamesPlayed: 0, wins: 0, streak: 0, bestPuzzle: 0 });
        if (!prefsSnap.exists()) transaction.set(prefsRef, { id: user.uid });
        return { created: true, profile };
      });
      if (outcome.conflict) continue;
      return { ...outcome.profile, id: user.uid, email: user.email || '' };
    }
    throw new Error('Could not claim a unique username. Try a different display name.');
  }
  async function updateCloudProfile(name, username) {
    const userRef = doc(cloudStore, 'users', currentUserId);
    const profileSnap = await getDoc(userRef);
    const oldProfile = profileSnap.exists() ? profileSnap.data() : (currentUser() || {});
    const newUsername = normalizeUsername(username);
    const newUsernameRef = doc(cloudStore, 'usernames', newUsername);
    const oldUsername = normalizeUsername(oldProfile.username || '');
    const oldUsernameRef = oldUsername ? doc(cloudStore, 'usernames', oldUsername) : null;
    await runTransaction(cloudStore, async transaction => {
      const refs = [transaction.get(newUsernameRef)];
      if (oldUsernameRef && oldUsername !== newUsername) refs.push(transaction.get(oldUsernameRef));
      const snaps = await Promise.all(refs);
      const newSnap = snaps[0];
      if (newSnap.exists() && newSnap.data().userId !== currentUserId) throw new Error('That username is already taken. Choose another one.');
      transaction.set(newUsernameRef, { id: newUsername, userId: currentUserId, createdAt: now() });
      if (oldUsernameRef && oldUsername !== newUsername && snaps[1]?.exists() && snaps[1].data().userId === currentUserId) transaction.delete(oldUsernameRef);
      transaction.set(userRef, { id: currentUserId, name, username: newUsername, avatar: initials(name), createdAt: oldProfile.createdAt || now() }, { merge: true });
    });
    if (db.users[currentUserId]) Object.assign(db.users[currentUserId], { name, username: newUsername, avatar: initials(name), email: firebaseAuth.currentUser?.email || '' });
    db.gcs.forEach(gc => gc.members.forEach(member => { if (member.userId === currentUserId) member.name = name; }));
    persist();
  }
  function scheduleCloudSync() {
    if (!cloudReady || applyingRemoteSnapshot || !firebaseAuth.currentUser) return;
    clearTimeout(cloudSyncTimer);
    cloudSyncTimer = setTimeout(() => { void syncCloudChanges(); }, 180);
  }
  async function syncCloudChanges() {
    if (!cloudReady || applyingRemoteSnapshot || !firebaseAuth.currentUser) return;
    if (cloudSyncRunning) { cloudSyncQueued = true; return; }
    cloudSyncRunning = true;
    try {
      do {
        cloudSyncQueued = false;
        const entries = buildCloudEntries();
        const changed = [...entries.values()].filter(entry => cloudBaseline.get(cloudKey(entry.path, entry.id)) !== stableStringify(entry.data));
        if (!changed.length) continue;
        for (let offset = 0; offset < changed.length; offset += 400) {
          const chunk = changed.slice(offset, offset + 400);
          const batch = writeBatch(cloudStore);
          chunk.forEach(entry => batch.set(doc(cloudStore, entry.path, entry.id), entry.data));
          await batch.commit();
          chunk.forEach(entry => cloudBaseline.set(cloudKey(entry.path, entry.id), stableStringify(entry.data)));
        }
      } while (cloudSyncQueued);
    } catch (error) {
      announceCloudError(error, 'Cloud save');
      // Keep the changed payload unacknowledged so the next mutation can retry.
    } finally {
      cloudSyncRunning = false;
      if (cloudSyncQueued) void syncCloudChanges();
    }
  }
  async function handleFirebaseAuthChange(user, runId) {
    stopCloudListeners();
    cloudReady = false;
    cloudBaseline.clear();
    if (!user) {
      currentUserId = '';
      privateConfessionOwnerIds.clear();
      db = blankDb();
      selectedGcId = ''; activeCoupleRoomId = ''; chatTargetId = ''; game = null; page = 'home';
      localStorage.removeItem(DB_KEY); localStorage.removeItem(SESSION_KEY);
      render();
      return;
    }
    currentUserId = user.uid;
    try {
      const profile = await ensureCloudProfile(user, pendingDisplayName);
      pendingDisplayName = '';
      if (runId !== authStateRun) return;
      await loadCloudData(user);
      if (runId !== authStateRun) return;
      if (profile?.name && !user.displayName) updateProfile(user, { displayName: profile.name }).catch(() => {});
      render();
      toast('Signed in. LOGIN INTO GCVERSE.');
    } catch (error) {
      announceCloudError(error, 'Firebase connection');
      render();
    }
  }
  function loginErrorMessage(error) {
    const code = error?.code || '';
    if (code === 'auth/invalid-email') return 'Enter a valid email address.';
    if (code === 'auth/weak-password') return 'Choose a password with at least 6 characters.';
    if (code === 'auth/invalid-credential' || code === 'auth/wrong-password') return 'Incorrect email or password. Check both and try again.';
    if (code === 'auth/too-many-requests') return 'Too many attempts. Wait a little and try again.';
    if (code === 'auth/popup-closed-by-user') return 'Google sign-in was closed before finishing.';
    if (code === 'auth/unauthorized-domain') return 'Add this site’s domain under Firebase Authentication → Settings → Authorized domains.';
    return error?.message || 'Authentication failed. Please try again.';
  }

  const gameInfo = {
    truth: { title: 'Truth & Dare', icon: '🎭', tag: '2 PLAYERS', desc: 'Two players, secret preferences, custom prompts and three rounds.', category: 'gc' },
    redflag: { title: 'Red Flag Detector', icon: '🚩', tag: '2–15 PLAYERS', desc: 'Judge realistic relationship situations: green, depends or red.', category: 'gc' },
    challenge: { title: 'Random Challenge', icon: '🎲', tag: '2–15 PLAYERS', desc: 'Four rounds. A different challenge for every player. No repeats.', category: 'gc' },
    tmkoc: { title: 'Get Your TMKOC Character', icon: '🇮🇳', tag: '2–10 PLAYERS', desc: 'Answer personality questions, then reveal your Gokuldham-style cast.', category: 'gc' },
    xo: { title: 'XO / Tic-Tac-Toe', icon: '❌⭕', tag: '2 PLAYERS', desc: 'A quick strategic match against a friend or the computer.', category: 'duo' },
    puzzle: { title: 'Puzzle Solve', icon: '🧩', tag: 'SOLO', desc: 'Logic, patterns and word puzzles. Build a streak and beat your best.', category: 'solo' }
  };

  const truthPrompts = [
    'What is one thing you pretend not to care about but actually do?',
    'What is the most embarrassing thing you have done to impress someone?',
    'Have you ever liked someone your friends would never expect?',
    'What is one message you typed but never sent?',
    'What is a first impression people often get wrong about you?',
    'What is the pettiest reason you have stopped replying to someone?',
    'What is something you wish people in this GC understood about you?',
    'Have you ever acted busy to avoid someone? Who was it?',
    'What is your most irrational relationship fear?',
    'What is a harmless secret you have kept for a long time?',
    'Who in this GC would you call first in a genuine emergency, and why?',
    'What is something you are jealous of but rarely admit?',
    'What is the worst excuse you have used to cancel plans?',
    'What is one red flag you have ignored in yourself?',
    'What is the most awkward thing that has happened during a date?',
    'What is one compliment you still remember?',
    'What is the biggest misunderstanding you have had with a friend?',
    'Have you ever judged someone and later realized you were wrong?',
    'What is something you would change about your texting habits?',
    'What is a small thing that instantly makes you lose interest in someone?'
  ];
  const darePrompts = [
    'Give a 15-second acceptance speech for an award you just invented.',
    'Speak like a breaking-news reporter for your next three messages.',
    'Send a voice note saying “I am the main character” in a dramatic voice.',
    'Describe your day as if it were a movie trailer.',
    'Make up a ridiculous superhero name and explain your power.',
    'Create a slogan for the GC as if you were selling a luxury product.',
    'Give someone in the GC a genuinely kind compliment.',
    'Explain your favourite food like you are a serious food critic.',
    'Write a motivational quote that makes absolutely no sense.',
    'Talk like a CEO for the next two minutes.',
    'Invent a fake holiday and explain its three rules.',
    'Tell a 20-second story using the words “train”, “pickle” and “moon”.',
    'Rename yourself with a ridiculous nickname for the next round.',
    'Do your best impression of a dramatic soap-opera character.',
    'Describe your personality using only five emojis.',
    'Pitch the GC a completely useless product in 20 seconds.',
    'Write a sentence where every word starts with the same letter.',
    'Explain why you should be the leader if this GC became a country.',
    'Give yourself a villain origin story in three sentences.',
    'Say something completely normal in the most dramatic way possible.'
  ];
  const redFlagScenarios = [
    { text: 'Your partner still talks to their ex regularly. They say they are just friends and do not hide the conversations.', area: 'Trust & exes' },
    { text: 'Your partner meets their ex for coffee but tells you only after you find out from someone else.', area: 'Trust & exes' },
    { text: 'Your partner refuses to share their phone password, but has never given you a reason to distrust them.', area: 'Privacy & boundaries' },
    { text: 'They cancel plans with you repeatedly, but almost never cancel plans with their friends.', area: 'Effort' },
    { text: 'They apologize after every argument but repeat the same hurtful behaviour without changing anything.', area: 'Communication' },
    { text: 'They want your live location all day but refuse to explain why they need it.', area: 'Control' },
    { text: 'Your partner flirts with other people as a joke and says “that is just my personality”.', area: 'Boundaries' },
    { text: 'They do not post your relationship online because they prefer to keep their private life private.', area: 'Social media' },
    { text: 'They post everything else online but deliberately pretend to be single around a specific person.', area: 'Social media' },
    { text: 'They stop replying during a disagreement and return hours later without acknowledging it.', area: 'Communication' },
    { text: 'Their close friend openly flirts with them. They do not flirt back, but also never set a boundary.', area: 'Boundaries' },
    { text: 'They expect you to pay most of the time and get annoyed when you suggest splitting costs.', area: 'Money' },
    { text: 'They bring up mistakes you made months ago in every new disagreement.', area: 'Conflict' },
    { text: 'They ask for space after a difficult conversation and explain when they will be ready to talk again.', area: 'Communication' },
    { text: 'They make jokes about your insecurities in front of friends, even after you asked them to stop.', area: 'Respect' },
    { text: 'They keep liking an ex’s public posts but have no direct contact with them.', area: 'Trust & exes' },
    { text: 'They expect you to reply immediately but regularly disappear for hours without explanation.', area: 'Double standards' },
    { text: 'They want you to cut off a friend simply because they feel threatened, without a specific incident.', area: 'Control' },
    { text: 'They admit they made a mistake, listen to the impact and consistently change the behaviour.', area: 'Accountability' },
    { text: 'They make major future plans with you, but avoid every conversation about what commitment means to them.', area: 'Commitment' },
    { text: 'They read your messages over your shoulder and say couples should not need privacy.', area: 'Privacy & boundaries' },
    { text: 'When upset, they insult you and later say you are too sensitive for being hurt.', area: 'Respect' },
    { text: 'They remember small details about you but sometimes need quiet time after social events.', area: 'Personality & needs' },
    { text: 'They repeatedly compare your appearance to people they find attractive.', area: 'Respect' },
    { text: 'They want to move quickly in the relationship and get angry when you ask to slow down.', area: 'Pace & consent' },
    { text: 'They never apologise first, even when they later admit they were wrong.', area: 'Accountability' },
    { text: 'They have close friends of a gender they are attracted to and are open about those friendships.', area: 'Trust & boundaries' },
    { text: 'They keep a major financial problem secret until you accidentally discover it.', area: 'Money & trust' },
    { text: 'They disagree with you respectfully and do not always need to win an argument.', area: 'Communication' },
    { text: 'They make you feel guilty for seeing friends or enjoying interests that do not include them.', area: 'Independence' }
  ];
  const challengePrompts = [
    ['Speak for 20 seconds without using the word “I”.', 'fun', 'easy'],
    ['Send your next message using only emojis.', 'digital', 'easy'],
    ['Describe yourself like a dramatic movie trailer.', 'fun', 'easy'],
    ['Explain your day using exactly five words.', 'fun', 'easy'],
    ['Make up a fake conspiracy theory about the GC.', 'chaos', 'medium'],
    ['Give yourself a ridiculous superhero name and power.', 'fun', 'easy'],
    ['Compliment someone you do not usually talk to.', 'social', 'easy'],
    ['Pick two people who would make the funniest duo and explain why.', 'social', 'medium'],
    ['Predict who in the GC will become famous first.', 'social', 'easy'],
    ['Give someone a fake award with a very specific title.', 'social', 'easy'],
    ['Choose someone who would be your teammate in a fictional heist.', 'social', 'medium'],
    ['Describe a GC member without saying their name; let people guess.', 'social', 'medium'],
    ['Change your GC nickname to something ridiculous for ten minutes.', 'digital', 'medium'],
    ['Type your next message using predictive text only.', 'digital', 'medium'],
    ['Send the third emoji in your recent emoji list.', 'digital', 'easy'],
    ['Write one sentence entirely in uppercase.', 'digital', 'easy'],
    ['Type your name backwards and send it.', 'digital', 'easy'],
    ['Send a message containing exactly ten words.', 'digital', 'medium'],
    ['Name five countries in ten seconds.', 'skill', 'medium'],
    ['Name five things beginning with S in ten seconds.', 'skill', 'easy'],
    ['Count backwards from 30 by threes.', 'skill', 'medium'],
    ['Name five movies without using the letter A.', 'skill', 'hard'],
    ['Name seven foods in ten seconds.', 'skill', 'medium'],
    ['Say five words that rhyme with “day”.', 'skill', 'easy'],
    ['Create a sentence where every word starts with the same letter.', 'skill', 'hard'],
    ['Give three uses for a completely useless object near you.', 'skill', 'medium'],
    ['Send “We need to talk…” then reveal it was a challenge after 15 seconds.', 'chaos', 'medium'],
    ['Write a breaking-news headline about the GC.', 'chaos', 'easy'],
    ['Give the GC a ridiculous new rule.', 'chaos', 'easy'],
    ['Talk like a corporate CEO for your next three messages.', 'chaos', 'medium'],
    ['React to the next message with the least appropriate harmless emoji.', 'chaos', 'medium'],
    ['Replace one random word in your next sentence with “potato”.', 'chaos', 'easy'],
    ['Make a fake announcement about something completely useless.', 'chaos', 'medium'],
    ['Defend an obviously terrible opinion for 20 seconds.', 'final', 'hard'],
    ['Create a 15-second story using three words picked by the group.', 'final', 'hard'],
    ['Invent a product and pitch it as if you need investors today.', 'final', 'hard'],
    ['Explain why you should be the leader if the GC became a country.', 'final', 'hard'],
    ['Give a 20-second acceptance speech for an award you invented.', 'final', 'medium'],
    ['Describe your whole personality without using adjectives.', 'final', 'hard'],
    ['Invent a new holiday and explain how people celebrate it.', 'final', 'medium'],
    ['Make an advertisement for the GC with a tagline.', 'final', 'medium'],
    ['Tell a villain origin story in exactly three sentences.', 'final', 'hard'],
    ['Pitch your life as a streaming series in 20 seconds.', 'final', 'medium'],
    ['Describe your favourite food as if it were a luxury car.', 'fun', 'easy'],
    ['Send a motivational quote that makes absolutely no sense.', 'fun', 'easy'],
    ['Give the last person who messaged a fictional superpower.', 'social', 'easy'],
    ['Pick who would survive longest in a zombie apocalypse.', 'social', 'easy'],
    ['Write a short poem about your phone.', 'fun', 'medium'],
    ['Explain your current mood using only a weather forecast.', 'fun', 'easy'],
    ['Write a 10-word conspiracy theory about a fictional object.', 'chaos', 'medium'],
    ['Pretend to be a museum guide presenting your desk or room.', 'fun', 'medium'],
    ['Invent a new emoji and explain what it means.', 'digital', 'easy'],
    ['Explain a simple thing as if you are teaching aliens.', 'fun', 'medium'],
    ['Name five apps in five seconds.', 'skill', 'easy'],
    ['Spell “definitely” backwards without looking it up.', 'skill', 'hard'],
    ['Create a tongue twister using your own name.', 'skill', 'medium'],
    ['Give everyone in the GC a fictional team role.', 'social', 'medium'],
    ['Describe a common object without naming it.', 'skill', 'medium'],
    ['Write a dramatic apology to your alarm clock.', 'fun', 'easy'],
    ['Give your current situation a clickbait title.', 'fun', 'easy'],
    ['Act like a sports commentator describing making a cup of tea.', 'chaos', 'medium'],
    ['Invent a fake app and describe its worst feature.', 'final', 'medium'],
    ['Make a five-second jingle for the GC.', 'final', 'medium'],
    ['Describe your week as a three-part documentary.', 'fun', 'medium'],
    ['Choose a fictional character to represent your current life.', 'social', 'easy'],
    ['Create a headline about your future self ten years from now.', 'final', 'medium'],
    ['Explain why your most-used app deserves an award.', 'digital', 'easy'],
    ['Give yourself a professional LinkedIn headline for a ridiculous job.', 'chaos', 'medium'],
    ['Name five things you would take to a deserted island in five seconds.', 'skill', 'medium'],
    ['Convince the GC that socks are a technological masterpiece.', 'final', 'hard'],
    ['Send a message with no letter “E”.', 'digital', 'hard'],
    ['Describe an ordinary task as if it were an Olympic event.', 'fun', 'medium'],
    ['Give a one-sentence review of your day like a movie critic.', 'fun', 'easy'],
    ['Create a fake law that would make the GC more organised.', 'chaos', 'medium'],
    ['Explain how you would handle a zombie outbreak using only items nearby.', 'final', 'hard'],
    ['Make a silly slogan for the person whose birthday is next.', 'social', 'easy'],
    ['Create a new word and define it.', 'skill', 'medium'],
    ['Deliver a weather forecast for the GC’s current mood.', 'chaos', 'easy'],
    ['Give a 15-second tutorial on something you are bad at.', 'fun', 'medium'],
    ['Invent a fictional country and describe its national sport.', 'final', 'medium'],
    ['Write a 6-word memoir about your life so far.', 'fun', 'medium'],
    ['Explain why you should receive a medal for surviving this week.', 'final', 'medium']
  ].map((item, index) => ({ id: `ch_${index + 1}`, text: item[0], category: item[1], difficulty: item[2] }));

  const tmkocCharacters = [
    { name: 'Jethalal', emoji: '😵‍💫', quote: 'Your life has more plot twists than your GC.', traits: { chaos: 91, drama: 88, confidence: 82, loyalty: 78, logic: 48 } },
    { name: 'Daya', emoji: '💃', quote: 'You bring enough energy for the entire society.', traits: { chaos: 86, drama: 70, confidence: 72, loyalty: 94, logic: 54 } },
    { name: 'Taarak Mehta', emoji: '🧠', quote: 'Everyone needs your advice; nobody follows it.', traits: { chaos: 35, drama: 40, confidence: 73, loyalty: 92, logic: 94 } },
    { name: 'Bhide', emoji: '📚', quote: 'Rules exist for a reason. You are that reason.', traits: { chaos: 28, drama: 58, confidence: 67, loyalty: 88, logic: 91 } },
    { name: 'Sodhi', emoji: '🎉', quote: 'If the plan is boring, you have a better plan.', traits: { chaos: 93, drama: 66, confidence: 89, loyalty: 87, logic: 55 } },
    { name: 'Iyer', emoji: '🔬', quote: 'You brought logic to a situation that needed snacks.', traits: { chaos: 43, drama: 48, confidence: 75, loyalty: 71, logic: 96 } },
    { name: 'Babita', emoji: '✨', quote: 'Calm, composed, and somehow at the centre of the plot.', traits: { chaos: 44, drama: 53, confidence: 93, loyalty: 74, logic: 83 } },
    { name: 'Popatlal', emoji: '📰', quote: 'Breaking news: you are overthinking again.', traits: { chaos: 63, drama: 82, confidence: 51, loyalty: 80, logic: 67 } },
    { name: 'Abdul', emoji: '🥤', quote: 'You know everybody’s business and keep the peace.', traits: { chaos: 51, drama: 41, confidence: 72, loyalty: 94, logic: 77 } },
    { name: 'Madhavi', emoji: '🌼', quote: 'Practical, dependable, and three steps ahead.', traits: { chaos: 38, drama: 45, confidence: 76, loyalty: 92, logic: 89 } }
  ];
  const tmkocQuestions = [
    { q: 'When the GC suddenly becomes chaotic, you…', options: [{ t: 'Add fuel to the fire', s: 'chaos' }, { t: 'Try to calm everyone down', s: 'loyalty' }, { t: 'Analyse who started it', s: 'logic' }, { t: 'Make it about you somehow', s: 'drama' }] },
    { q: 'Your friends ask for advice. You usually…', options: [{ t: 'Give a whole TED Talk', s: 'logic' }, { t: 'Make them laugh first', s: 'chaos' }, { t: 'Show up no matter what', s: 'loyalty' }, { t: 'Say what everyone is thinking', s: 'confidence' }] },
    { q: 'Your biggest strength is…', options: [{ t: 'I can handle the unexpected', s: 'chaos' }, { t: 'I am dependable', s: 'loyalty' }, { t: 'I think before acting', s: 'logic' }, { t: 'I can own any room', s: 'confidence' }] },
    { q: 'At a group event, you are…', options: [{ t: 'The loudest one there', s: 'drama' }, { t: 'Making sure everyone is included', s: 'loyalty' }, { t: 'Observing everything quietly', s: 'logic' }, { t: 'Somehow in the middle of a mess', s: 'chaos' }] },
    { q: 'When a plan goes wrong, you…', options: [{ t: 'Panic, then improvise', s: 'chaos' }, { t: 'Find the practical solution', s: 'logic' }, { t: 'Keep everyone together', s: 'loyalty' }, { t: 'Make a dramatic announcement', s: 'drama' }] },
    { q: 'Pick the line that sounds most like you.', options: [{ t: 'Relax. I have a plan.', s: 'confidence' }, { t: 'Let us look at the facts.', s: 'logic' }, { t: 'We are all in this together.', s: 'loyalty' }, { t: 'This is going to be a story.', s: 'drama' }] },
    { q: 'Your friends would describe you as…', options: [{ t: 'Unpredictable but fun', s: 'chaos' }, { t: 'The responsible one', s: 'logic' }, { t: 'A loyal all-rounder', s: 'loyalty' }, { t: 'A confident main character', s: 'confidence' }] }
  ];

  const puzzleQuestions = [
    { q: 'What number comes next?', display: '2  →  6  →  12  →  20  →  ?', options: ['24', '28', '30', '32'], answer: '30', explain: 'The pattern adds 4, then 6, then 8, then 10.' },
    { q: 'Complete the pattern.', display: '1  →  1  →  2  →  3  →  5  →  ?', options: ['7', '8', '9', '10'], answer: '8', explain: 'Each number is the sum of the previous two.' },
    { q: 'Which one does not belong?', display: 'Circle · Triangle · Square · Cube', options: ['Circle', 'Triangle', 'Square', 'Cube'], answer: 'Cube', explain: 'Cube is three-dimensional; the others are 2D shapes.' },
    { q: 'What comes next?', display: 'A  →  C  →  F  →  J  →  ?', options: ['M', 'N', 'O', 'P'], answer: 'O', explain: 'The jumps increase by one: +2, +3, +4, then +5.' },
    { q: 'A clock shows 3:15. What is the smaller angle between the hands?', display: '🕒  3:15', options: ['0°', '7.5°', '15°', '22.5°'], answer: '7.5°', explain: 'At 3:15 the minute hand is at 90° and the hour hand at 97.5°.' },
    { q: 'Which word completes the pair?', display: 'Book is to read as fork is to…', options: ['Draw', 'Eat', 'Write', 'Cook'], answer: 'Eat', explain: 'A book is used for reading; a fork is used for eating.' },
    { q: 'What number is missing?', display: '3,  6,  12,  24,  ?', options: ['36', '42', '48', '54'], answer: '48', explain: 'Each number doubles.' },
    { q: 'Rearrange the letters “LISTEN” to create a related word.', display: 'L I S T E N', options: ['Silent', 'Tinsel', 'Enlist', 'All of these'], answer: 'All of these', explain: 'All three words use the same six letters.' },
    { q: 'If all bloops are razzies and all razzies are lazzies, then…', display: 'Bloop → Razzies → Lazzies', options: ['All lazzies are bloops', 'All bloops are lazzies', 'No bloops are lazzies', 'Cannot tell'], answer: 'All bloops are lazzies', explain: 'If every bloop is a razzie and every razzie is a lazzy, all bloops are lazzies.' },
    { q: 'You have 3 switches outside a room and one bulb inside. You can enter the room only once. What helps identify the right switch?', display: '💡  +  3 switches', options: ['Flip all switches', 'Use light and bulb warmth', 'Guess randomly', 'No way at all'], answer: 'Use light and bulb warmth', explain: 'Leave one on, turn another off after it has warmed the bulb, then check both light and warmth.' },
    { q: 'What comes next?', display: '1,  4,  9,  16,  ?', options: ['20', '24', '25', '36'], answer: '25', explain: 'These are squares: 1², 2², 3², 4², 5².' },
    { q: 'Which is the odd one out?', display: 'Mercury · Venus · Mars · Moon', options: ['Mercury', 'Venus', 'Mars', 'Moon'], answer: 'Moon', explain: 'The Moon is a natural satellite, not a planet.' }
  ];

  function persist() {
    if (firebaseAuth.currentUser) {
      // Chat messages/confessions are short-lived; do not leave them in persistent browser storage.
      localStorage.removeItem(DB_KEY);
      localStorage.removeItem(SESSION_KEY);
      if (cloudReady && !applyingRemoteSnapshot) scheduleCloudSync();
      return;
    }
    localStorage.setItem(DB_KEY, JSON.stringify(db));
  }
  function currentUser() { return currentUserId ? db.users[currentUserId] : null; }
  function createUniqueUsername(name, excludeId = '') {
    const base = normalizeUsername(String(name || 'player').replace(/\s+/g, '.')) || 'player';
    const used = new Set(Object.values(db.users).filter(user => user.id !== excludeId).map(user => normalizeUsername(user.username)).filter(Boolean));
    if (!used.has(base) && base.length >= 3) return base;
    const stem = base.slice(0, 15) || 'player';
    for (let i = 2; i < 10000; i += 1) { const next = `${stem}${i}`; if (!used.has(next)) return next; }
    return `player${Math.random().toString(36).slice(2, 8)}`;
  }
  function migrateUsernames() {
    Object.values(db.users).forEach(user => {
      const candidate = normalizeUsername(user.username);
      const duplicate = candidate && Object.values(db.users).some(other => other.id !== user.id && normalizeUsername(other.username) === candidate);
      if (!candidate || candidate.length < 3 || duplicate) user.username = createUniqueUsername(user.name, user.id);
      else user.username = candidate;
    });
    persist();
  }
  function statsFor(userId = currentUserId) {
    db.stats[userId] ||= { xp: 0, gamesPlayed: 0, wins: 0, streak: 0, bestPuzzle: 0 };
    return db.stats[userId];
  }
  function prefsFor(userId = currentUserId) { db.userPrefs[userId] ||= {}; return db.userPrefs[userId]; }
  function myGcs() { return db.gcs.filter(gc => gc.members.some(member => member.userId === currentUserId)); }
  function getGc(id = selectedGcId) { return db.gcs.find(gc => gc.id === id) || null; }
  function memberFor(gc, userId = currentUserId) { return gc?.members.find(member => member.userId === userId) || null; }
  function liveMembers(gc) { return (gc?.members || []).filter(member => member.userId === currentUserId || (member.preview && member.online)); }
  function refreshIcons() { if (window.lucide?.createIcons) window.lucide.createIcons(); }
  function saveSession() { localStorage.removeItem(SESSION_KEY); }
  function cleanExpired() {
    const stamp = now();
    const oldConfessions = db.confessions.length;
    db.confessions = db.confessions.filter(item => item.expiresAt > stamp);
    db.gameSessions = db.gameSessions.filter(item => item.expiresAt > stamp);
    const oldMessages = db.messages.length;
    db.messages = db.messages.filter(item => item.expiresAt > stamp);
    const oldRooms = db.coupleRooms.length;
    db.coupleRooms = db.coupleRooms.filter(item => !item.expiresAt || item.expiresAt > stamp);
    if (oldConfessions !== db.confessions.length || oldMessages !== db.messages.length || oldRooms !== db.coupleRooms.length) persist();
  }
  function initialsAvatar(name, extraClass = '') { return `<span class="avatar ${extraClass}">${escapeHtml(initials(name))}</span>`; }
  function avatarWithDot(member) { return `<span style="position:relative;display:inline-flex">${initialsAvatar(member.name, 'avatar-small')}${member.userId === currentUserId ? '<i class="online-dot"></i>' : ''}</span>`; }
  function toast(message, type = 'success') {
    const node = $('#toast');
    $('#toastIcon').textContent = type === 'error' ? '!' : '✦';
    $('#toastMessage').textContent = message;
    node.classList.toggle('error', type === 'error');
    node.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => node.classList.remove('show'), 2800);
  }
  function showModal(content, opts = {}) {
    $('#modalContent').innerHTML = content;
    $('#modalOverlay').classList.add('open');
    $('#modalOverlay').setAttribute('aria-hidden', 'false');
    $('#modalDialog').dataset.modal = opts.type || '';
    document.body.style.overflow = 'hidden';
    refreshIcons();
    setTimeout(() => $('#modalContent input, #modalContent textarea, #modalContent select')?.focus(), 60);
  }
  function closeModal() {
    $('#modalOverlay').classList.remove('open');
    $('#modalOverlay').setAttribute('aria-hidden', 'true');
    document.body.style.overflow = '';
  }
  function initialsNameFallback(name = '') { return initials(name || 'GC'); }
  function setPage(next) {
    page = next;
    mobileNavOpen = false;
    $('#sidebar').classList.remove('mobile-open');
    $$('.side-link[data-nav]').forEach(el => el.classList.toggle('active', el.dataset.nav === next));
    $$('.mobile-bottom-nav button').forEach(el => el.classList.toggle('active', el.dataset.nav === next));
    const names = { home: 'Dashboard', games: 'Games', couples: 'Couples', chats: 'Chats', confessions: 'Confessions', leaderboard: 'Leaderboards', profile: 'Profile', game: 'Game room', gc: 'GC overview' };
    $('#breadcrumbCurrent').textContent = names[next] || 'Dashboard';
    renderPage();
    window.scrollTo({ top: 0, behavior: 'smooth' });
  }
  function ensureExtendedNavigation() {
    const sideNav = $('.side-nav');
    if (sideNav && !sideNav.querySelector('[data-nav="couples"]')) {
      const gamesLink = sideNav.querySelector('[data-nav="games"]');
      if (gamesLink) gamesLink.insertAdjacentHTML('afterend', '<button class="side-link" data-nav="couples"><i data-lucide="heart-handshake"></i><span>Couples</span></button><button class="side-link" data-nav="chats"><i data-lucide="messages-square"></i><span>Chats</span></button>');
    }
    const mobileNav = $('.mobile-bottom-nav');
    if (mobileNav && !mobileNav.querySelector('[data-nav="couples"]')) {
      mobileNav.insertAdjacentHTML('beforeend', '<button data-nav="couples"><i data-lucide="heart-handshake"></i><span>Couples</span></button><button data-nav="chats"><i data-lucide="messages-square"></i><span>Chats</span></button>');
      mobileNav.style.overflowX = 'auto';
      mobileNav.style.justifyContent = 'flex-start';
      $$('.mobile-bottom-nav button').forEach(button => { button.style.minWidth = '48px'; });
    }
  }

  function renderSidebar() {
    ensureExtendedNavigation();
    const gcs = myGcs();
    $('#sidebarGcCount').textContent = String(gcs.length);
    $('#sidebarGcList').innerHTML = gcs.slice(0, 5).map(gc => `<button class="sidebar-gc-link" data-action="open-gc" data-id="${gc.id}"><span class="sidebar-gc-emoji">${escapeHtml(gc.emoji || '🔥')}</span><span>${escapeHtml(gc.name)}</span><i class="tiny-presence ${memberFor(gc)?.userId === currentUserId ? 'online' : ''}"></i></button>`).join('') || '<p class="small muted" style="padding:0 11px">Your GCs will appear here.</p>';
    $('#topbarName').textContent = currentUser()?.name || 'Player';
    $('#topbarAvatar').textContent = initials(currentUser()?.name || 'P');
    $$('.side-link[data-nav]').forEach(el => el.classList.toggle('active', el.dataset.nav === page || (page === 'game' && el.dataset.nav === 'games') || (page === 'gc' && el.dataset.nav === 'home')));
    $$('.mobile-bottom-nav button').forEach(el => el.classList.toggle('active', el.dataset.nav === page || (page === 'game' && el.dataset.nav === 'games') || (page === 'gc' && el.dataset.nav === 'home')));
  }
  function render() {
    const signedIn = Boolean(currentUser());
    $('#authView').classList.toggle('hidden', signedIn);
    $('#appShell').classList.toggle('hidden', !signedIn);
    if (!signedIn) return refreshIcons();
    cleanExpired();
    renderSidebar();
    renderPage();
    refreshIcons();
  }

  function presenceLabel(gc) {
    const online = gc.members.filter(member => member.userId === currentUserId).length;
    const total = gc.members.length;
    if (online > 0) return `<span class="gc-presence"><i class="tiny-presence online"></i>${online} online · ${total} member${total === 1 ? '' : 's'}</span>`;
    return `<span class="gc-presence"><i class="tiny-presence"></i>Offline · ${total} member${total === 1 ? '' : 's'}</span>`;
  }
  function renderGcCard(gc, options = {}) {
    const online = gc.members.filter(member => member.userId === currentUserId).length;
    return `<article class="gc-card" data-id="${gc.id}">
      <div class="gc-card-top"><span class="gc-card-icon">${escapeHtml(gc.emoji || '🔥')}</span><span class="pill ${online ? 'mint' : ''}">${online ? 'ACTIVE' : 'OFFLINE'}</span></div>
      <h3>${escapeHtml(gc.name)}</h3><p class="members-line">${gc.members.length} member${gc.members.length === 1 ? '' : 's'} · ${gc.gamesPlayed || 0} games played</p>
      <div class="gc-card-foot">${presenceLabel(gc)}<button data-action="${options.selectOnly ? 'select-gc' : 'open-gc'}" data-id="${gc.id}">${options.selectOnly ? 'Choose GC' : 'Open GC'} <i data-lucide="arrow-up-right"></i></button></div>
    </article>`;
  }
  function renderMiniLeaderboard(gc = null) {
    let rows;
    if (gc) {
      rows = gc.members.map(member => ({ name: member.name, xp: Number(member.xp || 0), avatar: member.avatar || '👤', userId: member.userId })).sort((a, b) => b.xp - a.xp).slice(0, 5);
    } else {
      rows = Object.keys(db.users).map(id => ({ name: db.users[id].name, xp: Number(statsFor(id).xp || 0), avatar: db.users[id].avatar || '👤', userId: id })).sort((a, b) => b.xp - a.xp).slice(0, 5);
    }
    if (!rows.length) return '<div class="empty-state"><div class="empty-icon">🏆</div><h3>Leaderboard starts with you</h3><p>Play a game and earn the first XP.</p></div>';
    return `<div class="leader-preview-list">${rows.map((row, index) => `<div class="leader-row"><span class="rank-number">${String(index + 1).padStart(2, '0')}</span><div class="leader-name">${initialsAvatar(row.name, 'avatar-small')}<span>${escapeHtml(row.name)}${row.userId === currentUserId ? ' (you)' : ''}</span></div><span class="leader-xp">${Number(row.xp).toLocaleString()} XP</span></div>`).join('')}</div>`;
  }
  function renderHome() {
    const user = currentUser();
    const gcs = myGcs();
    const stats = statsFor();
    const continueGc = getGc(prefsFor().lastGcId) || gcs[0];
    const sessions = db.gameSessions.filter(item => item.userId === currentUserId).sort((a, b) => b.createdAt - a.createdAt).slice(0, 3);
    const dismissed = Boolean(prefsFor().creatorDismissed);
    const continueHtml = continueGc ? `<section class="continue-card card"><div class="continue-top"><span class="section-kicker">PICK UP WHERE YOU LEFT OFF</span><span class="pill purple">YOUR GC</span></div><div class="continue-body"><div class="gc-emblem">${escapeHtml(continueGc.emoji || '🔥')}</div><div class="continue-info"><h3>${escapeHtml(continueGc.name)}</h3><p>${continueGc.members.length} members · ${continueGc.gamesPlayed || 0} games played</p><span class="online-line"><i class="status-dot"></i>${continueGc.members.some(member => member.userId === currentUserId) ? 'You are active here' : 'No members online'}</span></div><button class="btn btn-primary" data-action="open-gc" data-id="${continueGc.id}">Continue playing <i data-lucide="arrow-up-right"></i></button></div></section>` : `<section class="continue-card card"><div class="continue-top"><span class="section-kicker">YOUR FIRST GAME STARTS HERE</span><span class="pill purple">WELCOME IN</span></div><div class="continue-body"><div class="gc-emblem">👥</div><div class="continue-info"><h3>Create your first GC</h3><p>Make a group once. Your membership stays connected to this account.</p><span class="online-line"><i class="status-dot"></i>Invite friends with a code</span></div><button class="btn btn-primary" data-action="create-gc">Create GC <i data-lucide="arrow-up-right"></i></button></div></section>`;
    return `<div class="welcome-row"><div class="welcome-copy"><span class="eyebrow"><span class="pulse-dot"></span> YOUR UNIVERSE IS READY</span><h1>Hey, ${escapeHtml(user.name.split(' ')[0])} <span>👋</span></h1><p>What are we getting into today?</p></div><div class="welcome-actions"><button class="btn btn-secondary" data-action="join-gc"><i data-lucide="link-2"></i> Join a GC</button><button class="btn btn-primary" data-action="create-gc"><i data-lucide="plus"></i> Create GC</button></div></div>
      <div class="dashboard-grid"><div class="dashboard-main-col">${continueHtml}
        <section><div class="section-head"><div><span class="section-kicker">YOUR GROUPS</span><h2>My GCs</h2></div><button class="inline-link" data-nav="games">Play with a GC <i data-lucide="arrow-up-right"></i></button></div>
          ${gcs.length ? `<div class="gc-cards-grid">${gcs.slice(0, 3).map(gc => renderGcCard(gc)).join('')}${gcs.length < 3 ? '<button class="add-gc-card" data-action="create-gc"><span class="add-circle"><i data-lucide="plus"></i></span><span>Create another GC</span></button>' : ''}</div>${gcs.length > 3 ? '<button class="btn btn-quiet" style="margin-top:12px" data-nav="games">View all groups</button>' : ''}` : `<div class="empty-state"><div class="empty-icon">👥</div><h3>No GCs yet</h3><p>Create a group or join one with an invite code. Once joined, it will stay in My GCs.</p><button class="btn btn-primary" data-action="create-gc"><i data-lucide="plus"></i> Create your first GC</button><button class="btn btn-quiet" data-action="join-gc">Join with code</button></div>`}
        </section>
        <section><div class="section-head"><div><span class="section-kicker">JUMP RIGHT IN</span><h2>Quick play</h2></div><button class="inline-link" data-nav="games">All games <i data-lucide="arrow-up-right"></i></button></div><div class="quick-play-grid"><button class="quick-play-card" data-action="quick-game" data-game="truth"><span class="quick-play-icon">🎭</span><strong>Truth & Dare</strong><small>Two-player showdown</small><span class="qp-arrow"><i data-lucide="arrow-up-right"></i></span></button><button class="quick-play-card" data-action="quick-game" data-game="redflag"><span class="quick-play-icon">🚩</span><strong>Red Flag Detector</strong><small>Debate the situation</small><span class="qp-arrow"><i data-lucide="arrow-up-right"></i></span></button><button class="quick-play-card" data-action="quick-game" data-game="challenge"><span class="quick-play-icon">🎲</span><strong>Random Challenge</strong><small>Four rounds of chaos</small><span class="qp-arrow"><i data-lucide="arrow-up-right"></i></span></button></div></section>
        <section><div class="section-head"><div><span class="section-kicker">RECENT ACTIVITY</span><h2>Recently played</h2></div></div>${sessions.length ? `<div class="card" style="padding:15px">${sessions.map(session => `<div class="leader-row" style="padding:9px 0;border-bottom:1px solid var(--line)"><span class="gc-card-icon" style="width:35px;height:35px;border-radius:11px;font-size:17px">${gameInfo[session.gameId]?.icon || '🎮'}</span><div class="leader-name" style="display:block"><span>${escapeHtml(gameInfo[session.gameId]?.title || session.gameId)}</span><small style="display:block;color:var(--muted);font-weight:400;margin-top:2px">${escapeHtml(session.gcName || 'Solo')} · ${ago(session.createdAt)}</small></div><span class="leader-xp">+${session.xp || 0} XP</span></div>`).join('')}</div>` : `<div class="empty-state"><div class="empty-icon">🎮</div><h3>Your highlights will show up here</h3><p>Finished games stay in your recent history for seven days. Your total XP remains on your profile.</p><button class="btn btn-secondary" data-nav="games">Explore games</button></div>`}</section>
      </div><aside class="dashboard-side-col">
        ${!dismissed ? `<section class="creator-card"><div class="creator-card-head"><div><span class="section-kicker">FROM THE CREATOR</span><h3>Useful things beyond the GC.</h3><p>Two other projects for your everyday life.</p></div><button class="icon-button" data-action="dismiss-creator" aria-label="Hide creator recommendations" style="width:29px;height:29px"><i data-lucide="x"></i></button></div><div class="creator-items"><a href="#" class="creator-item" data-action="open-project" data-project="studyflow"><span class="creator-logo study">📚</span><span class="creator-info"><strong>StudyFlow</strong><span>Wanna study smarter? Organise tasks, schedule and progress.</span></span><span class="creator-cta">Explore <i data-lucide="arrow-up-right"></i></span></a><a href="#" class="creator-item" data-action="open-project" data-project="spendnest"><span class="creator-logo spend">💰</span><span class="creator-info"><strong>SpendNest</strong><span>Wanna manage monthly money? Track expenses and spending.</span></span><span class="creator-cta">Explore <i data-lucide="arrow-up-right"></i></span></a></div><p class="dismiss-note">A small creator recommendation · dismiss anytime</p></section>` : `<section class="creator-card"><div class="creator-card-head" style="margin-bottom:0"><div><span class="section-kicker">FROM THE CREATOR</span><h3>StudyFlow & SpendNest</h3><p>Creator picks are hidden for now.</p></div><button class="text-link" data-action="show-creator">Show</button></div></section>`}
        <section class="card leader-preview"><div class="section-head" style="margin-bottom:16px"><div><span class="section-kicker">GLOBAL</span><h3>Leaderboard</h3></div><button class="inline-link" data-nav="leaderboard">View all <i data-lucide="arrow-up-right"></i></button></div>${renderMiniLeaderboard()}</section>
        <section><div class="section-head"><div><span class="section-kicker">YOUR STATS</span><h3>Player snapshot</h3></div></div><div class="stats-mini-grid"><div class="mini-stat"><span>Total XP</span><strong>${Number(stats.xp).toLocaleString()}</strong><em>↗</em></div><div class="mini-stat"><span>Games played</span><strong>${stats.gamesPlayed}</strong></div><div class="mini-stat"><span>GCs joined</span><strong>${gcs.length}</strong></div><div class="mini-stat"><span>Wins</span><strong>${stats.wins}</strong></div></div></section>
      </aside></div>`;
  }

  function renderGameCard(gameId) {
    const item = gameInfo[gameId];
    const classes = { truth: 'truth', redflag: 'redflag', challenge: 'challenge', tmkoc: 'tmkoc', xo: 'xo', puzzle: 'puzzle' };
    const foot = { truth: '3 rounds · Custom prompts', redflag: '30 realistic scenarios', challenge: '80+ tasks · 4 rounds', tmkoc: '10 unique character slots', xo: '2 players · vs computer', puzzle: '10 puzzles per run' };
    return `<article class="game-card ${classes[gameId] || ''}"><div class="game-card-top"><span class="game-icon-box">${item.icon}</span><span class="pill">${item.tag}</span></div><h3>${item.title}</h3><p>${item.desc}</p><div class="game-card-bottom"><span>${foot[gameId]}</span><button class="game-play-button" data-action="start-game" data-game="${gameId}">Open game <i data-lucide="arrow-up-right"></i></button></div></article>`;
  }
  function renderGames() {
    const gcs = myGcs();
    const selected = getGc(selectedGcId);
    if (selected && !memberFor(selected)) selectedGcId = '';
    const effective = getGc(selectedGcId);
    if (!effective) {
      return `<div class="page-intro"><div><span class="eyebrow"><span class="pulse-dot"></span> GAME LOBBY</span><h1>Choose your GC.</h1><p>Pick the group you want to play with. Your joined GCs stay saved here, so you will not need to add them again.</p></div><div class="page-actions"><button class="btn btn-secondary" data-action="join-gc"><i data-lucide="link-2"></i> Join a GC</button><button class="btn btn-primary" data-action="create-gc"><i data-lucide="plus"></i> Create GC</button></div></div>
        <div class="section-head"><div><span class="section-kicker">YOUR GROUPS</span><h2>Play with friends</h2></div><span class="pill">${gcs.length} saved</span></div>
        ${gcs.length ? `<div class="gc-selector-grid">${gcs.map(gc => `<button class="gc-select-card" data-action="select-gc" data-id="${gc.id}"><div class="gc-card-top"><span class="gc-card-icon">${escapeHtml(gc.emoji || '🔥')}</span><span class="pill ${gc.members.some(m => m.userId === currentUserId) ? 'mint' : ''}">${gc.members.some(m => m.userId === currentUserId) ? 'ACTIVE HERE' : 'OFFLINE'}</span></div><h3>${escapeHtml(gc.name)}</h3><p>${gc.members.length} members · ${gc.gamesPlayed || 0} games played</p><div class="gc-select-status">${presenceLabel(gc)}<b>Select GC <i data-lucide="arrow-up-right" style="width:12px;vertical-align:middle"></i></b></div></button>`).join('')}<button class="gc-action-card" data-action="create-gc"><span class="add-circle"><i data-lucide="plus"></i></span><strong>Create a new GC</strong><span>Start a new group</span></button><button class="gc-action-card" data-action="join-gc"><span class="add-circle"><i data-lucide="link-2"></i></span><strong>Join a GC</strong><span>Use an invite code</span></button></div>` : `<div class="empty-state"><div class="empty-icon">🎮</div><h3>You need a GC to start group games</h3><p>Create a group or join your friends with an invite code. Puzzle Solve and XO can also be played solo/from this page.</p><button class="btn btn-primary" data-action="create-gc">Create your first GC</button><button class="btn btn-secondary" data-action="join-gc">Join with code</button></div>`}
        <section class="game-section"><div class="game-section-title"><span>🧠</span><h2>Play solo</h2><p>No group needed</p></div><div class="game-grid">${renderGameCard('puzzle')}${renderGameCard('xo')}</div></section>`;
    }
    prefsFor().lastGcId = effective.id; persist();
    const activeCount = effective.members.filter(member => member.userId === currentUserId).length;
    const recent = db.gameSessions.filter(item => item.gcId === effective.id).sort((a, b) => b.createdAt - a.createdAt).slice(0, 3);
    return `<div class="game-room-header"><button class="back-link" data-action="switch-gc"><i data-lucide="arrow-left"></i> Switch GC</button><span class="gc-emblem">${escapeHtml(effective.emoji || '🔥')}</span><div class="room-header-copy"><span class="eyebrow">PLAYING IN YOUR GC</span><h1>${escapeHtml(effective.name)}</h1><p>${effective.members.length} members · ${activeCount ? 'You are active' : 'Currently offline'} · Invite code <b>${escapeHtml(effective.inviteCode)}</b></p></div><button class="btn btn-secondary" data-action="copy-code"><i data-lucide="copy"></i> Copy code</button></div>
      <section class="game-featured"><div class="featured-copy"><span class="pill orange">FEATURED GAME · 4 ROUNDS</span><h2>🎲 Random Challenge</h2><p>Every player gets a different task each round. 80+ prompts, four rounds, no repeat assignments in the same match.</p><div class="featured-meta"><span class="pill">2–15 players</span><span class="pill">80+ challenges</span><span class="pill">XP scoring</span></div><button class="btn btn-primary" data-action="start-game" data-game="challenge">Start a challenge <i data-lucide="arrow-up-right"></i></button></div><div class="featured-orb"><span>🎲</span></div></section>
      <section class="game-section" style="margin-top:0"><div class="game-section-title"><span>👥</span><h2>Play with your GC</h2><p>${effective.members.length} members available</p></div><div class="game-grid">${renderGameCard('truth')}${renderGameCard('redflag')}${renderGameCard('challenge')}${renderGameCard('tmkoc')}</div></section>
      <section class="game-section"><div class="game-section-title"><span>⚡</span><h2>Quick games</h2><p>Short sessions, easy to replay</p></div><div class="game-grid">${renderGameCard('xo')}${renderGameCard('puzzle')}</div></section>
      <section class="game-section"><div class="section-head"><div><span class="section-kicker">RECENTLY PLAYED</span><h2>In ${escapeHtml(effective.name)}</h2></div></div>${recent.length ? `<div class="card" style="padding:15px">${recent.map(item => `<div class="leader-row" style="padding:8px 0;border-bottom:1px solid var(--line)"><span class="gc-card-icon" style="width:34px;height:34px;font-size:17px">${gameInfo[item.gameId]?.icon || '🎮'}</span><div class="leader-name" style="display:block"><span>${escapeHtml(gameInfo[item.gameId]?.title || item.gameId)}</span><small style="display:block;color:var(--muted);font-weight:400">${ago(item.createdAt)}</small></div><span class="leader-xp">+${item.xp || 0} XP</span></div>`).join('')}</div>` : '<div class="empty-state"><div class="empty-icon">🕹️</div><h3>No recent games in this GC</h3><p>Start something. Your detailed game history will stay visible for seven days.</p></div>'}</section>`;
  }

  function renderConfessionPost(item) {
    const author = item.anonymous ? 'Anonymous' : (db.users[item.authorId]?.name || item.authorName || 'Member');
    const gc = item.scope === 'gc' ? getGc(item.gcId) : null;
    const likes = Array.isArray(item.likes) ? item.likes : [];
    const liked = likes.includes(currentUserId);
    return `<article class="confession-post"><div class="confession-post-top"><span class="confession-author-avatar">${item.anonymous ? '🤫' : escapeHtml(initials(author))}</span><div class="confession-author"><strong>${escapeHtml(author)}</strong><span>${item.scope === 'global' ? '🌐 Global' : `${escapeHtml(gc?.name || 'Your GC')}`} · ${ago(item.createdAt)}</span></div><span class="confession-expires"><i data-lucide="hourglass"></i>${remaining(item.expiresAt)}</span></div><div class="confession-content">${escapeHtml(item.content)}</div><div class="confession-post-foot"><div class="confession-reactions"><button class="reaction-btn ${liked ? 'active' : ''}" data-action="like-confession" data-id="${item.id}">♡ <span>${likes.length}</span></button><button class="reaction-btn" data-action="report-confession" data-id="${item.id}"><i data-lucide="flag"></i> Report</button></div><button class="post-menu" data-action="confession-menu" data-id="${item.id}">•••</button></div></article>`;
  }
  function visibleConfessions() {
    const myGcIds = new Set(myGcs().map(gc => gc.id));
    return db.confessions.filter(item => !(item.hiddenFor || []).includes(currentUserId) && (item.scope === 'global' || myGcIds.has(item.gcId)));
  }
  function renderConfessions() {
    const gcs = myGcs();
    const posts = visibleConfessions().filter(item => confessionScope === 'global' ? item.scope === 'global' : item.scope === 'gc');
    const filtered = posts.filter(item => confessionScope === 'global' || confessionGcFilter === 'all' || item.gcId === confessionGcFilter).sort((a, b) => b.createdAt - a.createdAt);
    const gcOptions = gcs.map(gc => `<option value="${gc.id}" ${confessionGcFilter === gc.id ? 'selected' : ''}>${escapeHtml(gc.emoji || '🔥')} ${escapeHtml(gc.name)}</option>`).join('');
    return `<div class="page-intro"><div><span class="eyebrow"><span class="pulse-dot"></span> SAY IT. LET IT GO.</span><h1>Confessions.</h1><p>Choose your circle or go global. Show your name or keep it hidden. Every confession expires after 24 hours.</p></div><div class="page-actions"><button class="btn btn-primary" data-action="create-confession"><i data-lucide="plus"></i> New confession</button></div></div>
      <div class="scope-tabs"><button class="tab-btn ${confessionScope === 'gcs' ? 'active' : ''}" data-action="confession-scope" data-scope="gcs">👥 Your GCs</button><button class="tab-btn ${confessionScope === 'global' ? 'active' : ''}" data-action="confession-scope" data-scope="global">🌐 Global feed</button></div>
      <div class="confession-layout"><div><div class="feed-toolbar"><h2>${confessionScope === 'global' ? 'Global confessions' : 'Inside your circles'}</h2><span>${filtered.length} active · auto-expires in 24h</span></div>${confessionScope === 'gcs' && gcs.length ? `<div style="margin-bottom:14px"><select id="confessionGcFilter" class="select-field" style="max-width:300px"><option value="all" ${confessionGcFilter === 'all' ? 'selected' : ''}>All my GCs</option>${gcOptions}</select></div>` : ''}<div class="confession-feed">${filtered.length ? filtered.map(renderConfessionPost).join('') : `<div class="empty-state"><div class="empty-icon">🤫</div><h3>${confessionScope === 'global' ? 'The global feed is quiet' : (gcs.length ? 'No confessions here yet' : 'Join or create a GC first')}</h3><p>${confessionScope === 'global' ? 'Be the first to start a conversation. Your post will disappear after 24 hours.' : (gcs.length ? 'Leave the first confession in one of your groups.' : 'GC-specific confessions are visible only to members of that GC.')}</p><button class="btn btn-secondary" data-action="create-confession">Write a confession</button></div>`}</div></div>
      <aside class="confession-side"><section class="card confession-compose-card"><span class="section-kicker">YOUR WORDS, YOUR RULES</span><h3>Got something to say?</h3><p>Pick a GC for an inside confession or use the global feed to reach GCVERSE users.</p><button class="btn btn-primary btn-full" data-action="create-confession">+ Create confession</button></section><section class="confession-note"><strong>🕒 24-hour lifetime</strong><p>Confessions leave the feed after 24 hours. Expired posts are hidden immediately in the UI and removed asynchronously by Firestore TTL.</p></section><section class="confession-note"><strong>🛡️ Anonymous to members</strong><p>Anonymous hides your name from readers. A private owner record is retained for future moderation tooling.</p></section></aside></div>`;
  }

  function renderLeaderboard() {
    const userRows = Object.keys(db.users).map(id => ({ id, name: db.users[id].name, xp: Number(statsFor(id).xp || 0), games: Number(statsFor(id).gamesPlayed || 0), wins: Number(statsFor(id).wins || 0) })).sort((a, b) => b.xp - a.xp);
    const myGc = getGc(selectedGcId) || myGcs()[0];
    const groupRows = myGc ? myGc.members.map(member => ({ id: member.userId, name: member.name, xp: Number(member.xp || 0), games: Number(member.gamesPlayed || 0), wins: Number(member.wins || 0) })).sort((a, b) => b.xp - a.xp) : [];
    const rowsHtml = rows => rows.length ? `<table class="leaderboard-table"><thead><tr><th>Rank</th><th>Player</th><th>Games</th><th>Wins</th><th>Total XP</th></tr></thead><tbody>${rows.map((row, index) => `<tr><td><span class="table-rank">${String(index + 1).padStart(2, '0')}</span></td><td><div class="table-player">${initialsAvatar(row.name)}<span>${escapeHtml(row.name)}${row.id === currentUserId ? ' <small style="color:var(--muted);font-weight:400">you</small>' : ''}</span></div></td><td>${row.games}</td><td>${row.wins}</td><td class="table-xp">${row.xp.toLocaleString()}</td></tr>`).join('')}</tbody></table>` : '<div class="empty-state"><div class="empty-icon">🏆</div><h3>Nothing ranked yet</h3><p>Finish games to earn XP and build the leaderboard.</p></div>';
    const podiumRows = userRows.slice(0, 3);
    return `<div class="page-intro"><div><span class="eyebrow">CLIMB THE RANKS</span><h1>Leaderboards.</h1><p>XP stays on your profile even when detailed game sessions expire after seven days.</p></div><div class="page-actions"><button class="btn btn-secondary" data-nav="games"><i data-lucide="gamepad-2"></i> Play for XP</button></div></div>
      <div class="leaderboard-layout"><section class="card leaderboard-table-card"><div class="section-head"><div><span class="section-kicker">GLOBAL RANK</span><h2>Players</h2></div><span class="pill purple">${userRows.length} GCVERSE accounts</span></div>${rowsHtml(userRows)}</section><aside class="podium-card"><span class="section-kicker">TOP PLAYERS</span><h3>Current podium</h3><p>The highest XP totals synced from Firestore.</p>${podiumRows.length ? `<div class="podium-visual">${[podiumRows[1], podiumRows[0], podiumRows[2]].map((row, i) => row ? `<div class="podium-person ${i === 0 ? 'second' : i === 1 ? 'first' : 'third'}">${initialsAvatar(row.name)}<strong>${escapeHtml(row.name.split(' ')[0])}</strong><small>${row.xp} XP</small><div class="podium-step"></div></div>` : '<div class="podium-person"><span class="avatar avatar-medium">?</span><strong>—</strong><small>0 XP</small><div class="podium-step"></div></div>').join('')}</div>` : '<div class="empty-state"><div class="empty-icon">✨</div><h3>First place is open</h3><p>Play a game to start your score.</p></div>'}<div class="setting-row"><div><strong>GC leaderboard</strong><p>${myGc ? `Current group: ${escapeHtml(myGc.name)}` : 'Create or join a GC to unlock group rankings.'}</p></div>${myGc ? '<button class="btn btn-quiet" data-action="gc-leaderboard">View</button>' : '<button class="btn btn-quiet" data-action="create-gc">Create</button>'}</div></aside></div><section class="game-section"><div class="section-head"><div><span class="section-kicker">YOUR CURRENT GROUP</span><h2>${myGc ? escapeHtml(myGc.name) : 'GC leaderboard'}</h2></div>${myGc ? `<button class="inline-link" data-action="open-gc" data-id="${myGc.id}">Open GC <i data-lucide="arrow-up-right"></i></button>` : ''}</div>${myGc ? `<div class="card leaderboard-table-card">${rowsHtml(groupRows)}</div>` : '<div class="empty-state"><div class="empty-icon">👥</div><h3>No group selected</h3><p>Join a GC to see its own leaderboard.</p></div>'}</section>`;
  }

  function renderProfile() {
    const user = currentUser();
    const stats = statsFor();
    const gcs = myGcs();
    const recent = db.gameSessions.filter(item => item.userId === currentUserId).sort((a, b) => b.createdAt - a.createdAt).slice(0, 5);
    return `<div class="page-intro"><div><span class="eyebrow">YOUR PLAYER CARD</span><h1>Profile & settings.</h1><p>Your account details, groups, player stats and preferences.</p></div><div class="page-actions"><button class="btn btn-secondary" id="signOutOnProfile" data-action="sign-out"><i data-lucide="log-out"></i> Sign out</button></div></div>
      <section class="profile-hero"><span class="avatar">${escapeHtml(initials(user.name))}</span><div class="profile-main"><h2>${escapeHtml(user.name)}</h2><p>@${escapeHtml(user.username || 'player')} · ${escapeHtml(user.email || (firebaseAuth.currentUser?.email || 'Account'))} · Cloud profile</p><span class="pill mint"><i data-lucide="shield-check" style="width:12px"></i>Authentication Done</span></div><div class="stats-mini-grid" style="min-width:min(310px,42%)"><div class="mini-stat"><span>Total XP</span><strong>${stats.xp.toLocaleString()}</strong></div><div class="mini-stat"><span>Games played</span><strong>${stats.gamesPlayed}</strong></div></div></section>
      <div class="profile-layout"><section class="card settings-card"><h3>Profile information</h3><form id="profileForm" class="settings-form"><label>Display name<input class="field" name="displayName" maxlength="24" required value="${escapeHtml(user.name)}"></label><label>Username<input class="field" name="username" minlength="3" maxlength="20" pattern="[a-zA-Z0-9._]+" required value="${escapeHtml(user.username || '')}" placeholder="your.handle"><small class="form-help">3–20 characters: letters, numbers, dots or underscores. Usernames are claimed atomically in Firestore.</small></label><label>Email address<input class="field" name="email" value="${escapeHtml(user.email || '')}" disabled></label><button class="btn btn-primary" type="submit">Save profile changes</button></form><div class="setting-row"><div><strong>Creator recommendations</strong><p>StudyFlow and SpendNest cards on your dashboard.</p></div><input id="creatorToggle" class="toggle" type="checkbox" ${prefsFor().creatorDismissed ? '' : 'checked'} aria-label="Show creator recommendations"></div><div class="setting-row"><div><strong>Short-lived game history</strong><p>Detailed sessions are retained for seven days in the planned backend.</p></div><span class="pill">7 DAYS</span></div><div class="setting-row"><div><strong>Confessions lifetime</strong><p>Confession posts expire after 24 hours.</p></div><span class="pill">24 HOURS</span></div></section>
      <div style="display:grid;gap:15px"><section class="card settings-card"><h3>My GCs <span class="pill">${gcs.length}</span></h3>${gcs.length ? gcs.map(gc => `<div class="leader-row" style="margin:12px 0"> <span class="gc-card-icon" style="width:36px;height:36px;font-size:18px">${escapeHtml(gc.emoji || '🔥')}</span><div class="leader-name" style="display:block"><span>${escapeHtml(gc.name)}</span><small style="display:block;color:var(--muted);font-weight:400">${gc.members.length} members · invite ${escapeHtml(gc.inviteCode)}</small></div><button class="text-link" data-action="open-gc" data-id="${gc.id}">Open</button></div>`).join('') : '<p class="small muted">No groups joined yet.</p>'}<div class="modal-actions" style="margin-top:16px"><button class="btn btn-secondary" data-action="join-gc">Join GC</button><button class="btn btn-primary" data-action="create-gc">Create GC</button></div></section><section class="card settings-card"><h3>Recent games</h3>${recent.length ? recent.map(item => `<div class="leader-row" style="margin:12px 0"><span class="gc-card-icon" style="width:34px;height:34px;font-size:16px">${gameInfo[item.gameId]?.icon || '🎮'}</span><div class="leader-name" style="display:block"><span>${escapeHtml(gameInfo[item.gameId]?.title || item.gameId)}</span><small style="display:block;color:var(--muted);font-weight:400">${ago(item.createdAt)}</small></div><strong class="leader-xp">+${item.xp || 0}</strong></div>`).join('') : '<p class="small muted">No completed games yet.</p>'}</section></div></div>`;
  }

  function renderGcOverview() {
    const gc = getGc(selectedGcId);
    if (!gc) { setPage('home'); return renderHome(); }
    const members = gc.members;
    const memberRows = members.map(member => `<div class="modal-member-row">${initialsAvatar(member.name)}<span>${escapeHtml(member.name)}${member.userId === currentUserId ? ' (you)' : ''}</span><small>${member.role === 'owner' ? 'Owner' : member.preview ? 'Preview member' : 'Member'}</small>${member.userId === currentUserId ? '<span class="pill mint">YOU</span>' : ''}</div>`).join('');
    return `<div class="game-room-header"><button class="back-link" data-nav="home"><i data-lucide="arrow-left"></i> Dashboard</button><span class="gc-emblem">${escapeHtml(gc.emoji || '🔥')}</span><div class="room-header-copy"><span class="eyebrow">GROUP OVERVIEW</span><h1>${escapeHtml(gc.name)}</h1><p>${members.length} members · invite code <b>${escapeHtml(gc.inviteCode)}</b></p></div><button class="btn btn-primary" data-action="select-gc" data-id="${gc.id}">Play with this GC <i data-lucide="arrow-up-right"></i></button></div>
      <div class="dashboard-grid"><div class="dashboard-main-col"><section class="card settings-card"><div class="section-head"><div><span class="section-kicker">MEMBERS</span><h2>Inside the GC</h2></div><button class="btn btn-secondary" data-action="copy-code"><i data-lucide="copy"></i> Copy invite code</button></div><div class="modal-member-list">${memberRows}</div><p class="form-help">Share the invite code so friends can join from their own GCVERSE account. Membership stays saved; no need to add them again.</p></section><section><div class="section-head"><div><span class="section-kicker">YOUR GC GAMES</span><h2>Pick a game</h2></div></div><div class="game-grid">${renderGameCard('truth')}${renderGameCard('redflag')}${renderGameCard('challenge')}${renderGameCard('tmkoc')}</div></section></div><aside class="dashboard-side-col"><section class="card settings-card"><span class="section-kicker">GC STATS</span><div class="stats-mini-grid" style="margin-top:13px"><div class="mini-stat"><span>Members</span><strong>${members.length}</strong></div><div class="mini-stat"><span>Games played</span><strong>${gc.gamesPlayed || 0}</strong></div><div class="mini-stat"><span>Total XP</span><strong>${members.reduce((sum, m) => sum + (m.xp || 0), 0)}</strong></div><div class="mini-stat"><span>Created</span><strong style="font-size:15px">${formatDate(gc.createdAt)}</strong></div></div></section><section class="card settings-card"><div class="section-head"><div><span class="section-kicker">GROUP RANK</span><h3>${escapeHtml(gc.name)}</h3></div><button class="text-link" data-action="gc-leaderboard">Full rank</button></div>${renderMiniLeaderboard(gc)}</section><button class="btn btn-secondary" data-action="join-gc"><i data-lucide="users"></i> Join another GC</button></aside></div>`;
  }

  const coupleGameInfo = {
    quiz: { title: 'Couples Quiz', icon: '💞', desc: 'Answer the same questions separately and compare your picks.' },
    thisorthat: { title: 'This or That', icon: '⚖️', desc: 'Quick choices, surprising differences, no wrong answers.' },
    longdistance: { title: 'Long-Distance Couples', icon: '🌙', desc: '30 questions across cute, flirty, honest and deeper stages.' },
    truthdare: { title: 'Couples Truth or Dare', icon: '🎭', desc: 'Take turns choosing truth or dare in a private room.' },
    knowme: { title: 'Do You Really Know Me?', icon: '🧠', desc: 'Predict your partner’s answers, then compare.' }
  };

  const coupleQuestions = {
    quiz: [
      { q: 'What would be your ideal date together?', options: ['A quiet movie night', 'A spontaneous road trip', 'A fancy dinner', 'A walk and deep talks'] },
      { q: 'Which small gesture feels most meaningful?', options: ['A thoughtful message', 'Remembering tiny details', 'Making time for me', 'A surprise snack or gift'] },
      { q: 'What kind of trip would you pick?', options: ['Mountains', 'Beach', 'A new city', 'A cosy stay-in weekend'] },
      { q: 'How do you prefer to resolve a disagreement?', options: ['Talk immediately', 'Take a little time first', 'Go for a walk together', 'Write out my thoughts'] },
      { q: 'What is your favourite way to feel supported?', options: ['Words of reassurance', 'Practical help', 'Quality time', 'A hug or affection'] },
      { q: 'Which shared activity sounds best?', options: ['Cooking together', 'Gaming together', 'Exploring somewhere new', 'Watching a series'] },
      { q: 'What makes a surprise feel special?', options: ['It is personal', 'It is funny', 'It took effort', 'It is completely unexpected'] },
      { q: 'What would you save from a perfect day?', options: ['Photos', 'A voice note', 'A little souvenir', 'The memory, no proof needed'] },
      { q: 'Which couple habit would you choose?', options: ['Good-morning messages', 'Weekly date night', 'Shared playlist', 'Daily check-in'] },
      { q: 'What matters most for a strong relationship?', options: ['Trust', 'Communication', 'Effort', 'Laughter'] }
    ],
    thisorthat: [
      { q: 'Choose your vibe for a date.', options: ['Cosy night in 🛋️', 'Night out ✨'] },
      { q: 'What would you rather receive?', options: ['A long paragraph 💌', 'A surprise call 📞'] },
      { q: 'Ideal way to spend a free day?', options: ['Adventure outside 🌍', 'Stay in together 🧸'] },
      { q: 'Which sounds more romantic?', options: ['Sunset walk 🌅', 'Stargazing 🌌'] },
      { q: 'Pick your communication style.', options: ['Texts all day 💬', 'One long call 🎧'] },
      { q: 'Which gift means more?', options: ['Something handmade 🎁', 'An experience together 🎟️'] },
      { q: 'When upset, what helps most?', options: ['Talk it out now 🫶', 'A little space first 🌿'] },
      { q: 'Choose a shared hobby.', options: ['Gaming 🎮', 'Cooking 🍜'] },
      { q: 'Which would you prefer?', options: ['Plan everything 📅', 'Be spontaneous 🎲'] },
      { q: 'A perfect anniversary is…', options: ['Private and meaningful 💗', 'Big and memorable 🎉'] }
    ],
    longdistance: [
      ['Cute & flirty', 'What’s the first thing about me that you found attractive?'],
      ['Cute & flirty', 'If I were next to you right now, what would you want us to do first?'],
      ['Cute & flirty', 'Which one of my habits secretly makes you smile?'],
      ['Cute & flirty', 'What’s one compliment from me that you would never get tired of hearing?'],
      ['Cute & flirty', 'Who usually gets more flustered during a flirty conversation?'],
      ['Cute & flirty', 'What’s your favourite memory of us talking late at night?'],
      ['Cute & flirty', 'If we had 24 hours together with no interruptions, how would you plan our day?'],
      ['Cute & flirty', 'Which of my looks or outfits do you find the most attractive?'],
      ['Cute & flirty', 'What’s something romantic you’ve wanted to do with me but haven’t told me?'],
      ['Cute & flirty', 'Who do you think would make the first move if we met for the first time today?'],
      ['Teasing & tension', 'Have you ever reread our old chats because you missed me?'],
      ['Teasing & tension', 'What’s something I do that makes you jealous, even if you don’t admit it?'],
      ['Teasing & tension', 'Have you ever acted busy just to see whether I’d miss you?'],
      ['Teasing & tension', 'What’s the boldest romantic thought you’ve had about our next meeting?'],
      ['Teasing & tension', 'If I whispered something flirty to you in public, would you blush or flirt back?'],
      ['Teasing & tension', 'Which gets to you more: my voice, my eyes or the way I text?'],
      ['Teasing & tension', 'Have you ever wanted my attention while pretending you didn’t care?'],
      ['Teasing & tension', 'What’s one message from me that could instantly improve your mood?'],
      ['Teasing & tension', 'If someone flirted with me in front of you, what would your honest reaction be?'],
      ['Teasing & tension', 'What’s one thing you wish I would initiate more often in our relationship?'],
      ['Honest & deeper', 'What’s one thought about us that you’ve been too nervous to say out loud?'],
      ['Honest & deeper', 'Have you ever felt insecure about someone from my past?'],
      ['Honest & deeper', 'What’s the biggest temptation you think could test our long-distance relationship?'],
      ['Honest & deeper', 'Have you ever hidden that you were upset because you didn’t want to seem needy?'],
      ['Honest & deeper', 'What’s one boundary you would never want us to cross with other people?'],
      ['Honest & deeper', 'If we had a serious fight right before sleeping, would you want to resolve it immediately or take some space?'],
      ['Honest & deeper', 'What’s something that could make you feel emotionally distant from me, even if we still talked every day?'],
      ['Honest & deeper', 'Have you ever worried that one day distance might change our feelings?'],
      ['Honest & deeper', 'What’s one truth about love or attraction that you find difficult to admit?'],
      ['Honest & deeper', 'If I asked you what scares you most about losing me, what would your honest answer be?']
    ].map(([category, q]) => ({ q, category, freeText: true })),
    truthdare: [
      { q: 'Pick the energy for this round.', options: ['Truth 😇', 'Dare 😈', 'Random pick 🎲'] },
      { q: 'Choose a mini challenge.', options: ['Give a sincere compliment', 'Share an embarrassing story', 'Do a dramatic voice note', 'Reveal a harmless secret'] },
      { q: 'Choose the next move.', options: ['Ask a bold question', 'Recreate your first impression', 'Send a cute voice note', 'Let your partner choose'] },
      { q: 'Pick one honest answer.', options: ['What do you appreciate most?', 'What made you smile recently?', 'What should we do together next?', 'What do you wish we did more?'] },
      { q: 'Final round: choose your dare.', options: ['Write a 10-word love note', 'Give a funny nickname', 'Describe your partner in 3 emojis', 'Plan your next virtual date'] }
    ],
    knowme: [
      { q: 'What would I choose for a free evening?', options: ['Go out with friends', 'Stay in and relax', 'Try something new', 'Catch up on work'] },
      { q: 'What usually cheers me up fastest?', options: ['Food', 'A good conversation', 'A funny video', 'Some quiet time'] },
      { q: 'Which kind of gift would I love?', options: ['Something useful', 'Something personal', 'An experience', 'A surprise snack'] },
      { q: 'What is my likely travel pick?', options: ['Mountains', 'Beach', 'City break', 'Road trip'] },
      { q: 'What do I value most in communication?', options: ['Quick replies', 'Honesty', 'Thoughtfulness', 'Being listened to'] },
      { q: 'What would I pick for a perfect meal?', options: ['Street food', 'Homemade comfort food', 'Fancy restaurant', 'Dessert first'] },
      { q: 'How do I recharge after a hard day?', options: ['Talk to someone', 'Be alone for a while', 'Watch something', 'Go for a walk'] },
      { q: 'What kind of plans suit me best?', options: ['A clear plan', 'Spontaneous plans', 'A mix of both', 'No plan at all'] }
    ]
  };

  function coupleRoom(id = activeCoupleRoomId) { return db.coupleRooms.find(room => room.id === id) || null; }
  function activeCoupleQuestion(room) {
    const questions = coupleQuestions[room.gameId] || coupleQuestions.quiz;
    return questions[room.index % questions.length];
  }
  function coupleOtherId(room) { return room.ownerId === currentUserId ? room.partnerId : room.ownerId; }
  function coupleOtherName(room) { const otherId = coupleOtherId(room); return db.users[otherId]?.name || 'Your partner'; }
  function coupleBothAnswered(room) {
    const response = room.responses?.[room.index] || {};
    return Boolean(response[room.ownerId] !== undefined && room.partnerId && response[room.partnerId] !== undefined);
  }
  function renderCouples() {
    const active = coupleRoom();
    if (active) return renderCoupleRoom(active);
    const recentRooms = db.coupleRooms.filter(room => room.ownerId === currentUserId || room.partnerId === currentUserId).sort((a,b) => b.createdAt - a.createdAt).slice(0,4);
    return `<div class="page-intro"><div><span class="eyebrow"><span class="pulse-dot"></span> JUST YOU TWO</span><h1>Couples corner. 💗</h1><p>Private two-player games for partners in the same place or miles apart. Create a room and share its code.</p></div><div class="page-actions"><button class="btn btn-secondary" data-action="join-couple-room"><i data-lucide="key-round"></i> Join room</button></div></div>
      <div class="dashboard-grid"><div class="dashboard-main-col"><section class="game-section" style="margin-top:0"><div class="section-head"><div><span class="section-kicker">FIVE WAYS TO CONNECT</span><h2>Choose your game</h2></div></div><div class="game-grid">${Object.entries(coupleGameInfo).map(([id,item]) => `<article class="game-card"><div class="game-card-top"><span class="game-icon-box">${item.icon}</span><span class="pill">2 PLAYERS</span></div><h3>${escapeHtml(item.title)}</h3><p>${escapeHtml(item.desc)}</p><div class="game-card-bottom"><span>Private room · Shareable code</span><button class="game-play-button" data-action="start-couple-game" data-game="${id}">Start game <i data-lucide="arrow-up-right"></i></button></div></article>`).join('')}</div></section></div><aside class="dashboard-side-col"><section class="card settings-card"><span class="section-kicker">HOW IT WORKS</span><h3 style="margin-top:8px">A room for two</h3><p class="muted small">One person creates a room, then shares the six-character code. Each partner answers separately; responses stay hidden until both have answered.</p><div class="setting-row"><div><strong>Private by room code</strong><p>No GC membership required.</p></div><span class="pill">2P</span></div><div class="setting-row"><div><strong>Long-distance mode</strong><p>30 prompts in three stages.</p></div><span class="pill">30 Qs</span></div></section>${recentRooms.length ? `<section class="card settings-card"><h3>Recent rooms</h3>${recentRooms.map(room => `<div class="leader-row" style="margin:10px 0"><span class="gc-card-icon">${coupleGameInfo[room.gameId]?.icon || '💗'}</span><div class="leader-name" style="display:block"><span>${escapeHtml(coupleGameInfo[room.gameId]?.title || room.gameId)}</span><small style="display:block;color:var(--muted);font-weight:400">Code ${escapeHtml(room.code)} · ${room.partnerId ? 'Partner joined' : 'Waiting for partner'}</small></div><button class="text-link" data-action="resume-couple-room" data-id="${room.id}">Open</button></div>`).join('')}</section>` : ''}</aside></div>`;
  }

  function renderCoupleRoom(room) {
    if (room.ownerId !== currentUserId && room.partnerId !== currentUserId) { activeCoupleRoomId = ''; return renderCouples(); }
    const info = coupleGameInfo[room.gameId] || coupleGameInfo.quiz;
    const question = activeCoupleQuestion(room);
    const responses = room.responses?.[room.index] || {};
    const answered = responses[currentUserId] !== undefined;
    const both = coupleBothAnswered(room);
    const myRole = room.ownerId === currentUserId ? 'You (host)' : 'You';
    const otherLabel = coupleOtherName(room);
    const stageBadge = question.category ? `<span class="pill purple">${escapeHtml(question.category)}</span>` : `<span class="pill purple">QUESTION ${room.index + 1} / ${(coupleQuestions[room.gameId] || coupleQuestions.quiz).length}</span>`;
    const responseSummary = both ? `<div class="card" style="padding:15px;margin-top:14px"><div class="section-kicker">ANSWERS REVEALED</div><div class="setting-row"><div><strong>${escapeHtml(db.users[room.ownerId]?.name || 'Host')}</strong><p style="white-space:pre-wrap">${escapeHtml(responses[room.ownerId])}</p></div></div><div class="setting-row"><div><strong>${escapeHtml(db.users[room.partnerId]?.name || 'Partner')}</strong><p style="white-space:pre-wrap">${escapeHtml(responses[room.partnerId])}</p></div></div></div>` : '';
    const input = answered ? `<div class="empty-state" style="padding:22px"><div class="empty-icon">🔒</div><h3>Answer locked in</h3><p>Your response is hidden until both players answer. Ask your partner to join using the room code.</p></div>` : question.freeText ? `<form id="coupleAnswerForm" class="settings-form"><label>Your answer<textarea class="textarea-field" name="answer" required maxlength="1000" rows="4" placeholder="Be honest. Your answer stays hidden until both respond…"></textarea></label><button class="btn btn-primary" type="submit">Lock in answer <i data-lucide="lock-keyhole"></i></button></form>` : `<div class="choice-grid">${question.options.map((option,index) => `<button class="choice-card" data-action="couple-answer-choice" data-answer="${escapeHtml(option)}"><span class="choice-emoji">${['💗','✨','🌙','🎲'][index % 4]}</span><strong>${escapeHtml(option)}</strong></button>`).join('')}</div>`;
    return `<div class="game-room-header"><button class="back-link" data-action="couple-back"><i data-lucide="arrow-left"></i> All couples games</button><span class="gc-emblem">${info.icon}</span><div class="room-header-copy"><span class="eyebrow">PRIVATE COUPLE ROOM</span><h1>${escapeHtml(info.title)}</h1><p>Room code <b>${escapeHtml(room.code)}</b> · ${room.partnerId ? `Partner: ${escapeHtml(otherLabel)}` : 'Waiting for your partner to join'}</p></div><button class="btn btn-secondary" data-action="copy-couple-code" data-id="${room.id}"><i data-lucide="copy"></i> Copy code</button></div>
      <section class="stage-panel"><div class="stage-topline"><span class="pill mint">${room.partnerId ? '2 PLAYERS CONNECTED' : 'WAITING FOR PARTNER'}</span>${stageBadge}</div><div class="stage-question"><span class="big-emoji">${info.icon}</span><h2>${escapeHtml(question.q)}</h2><p>${room.partnerId ? 'Both partners answer independently. Neither answer is shown until both have locked in.' : 'Share this room code with your partner. Your partner can join from another device using the room code.'}</p></div>${input}${responseSummary}${both ? `<div class="stage-actions" style="margin-top:18px"><button class="btn btn-primary" data-action="couple-next">${room.index + 1 >= (coupleQuestions[room.gameId] || coupleQuestions.quiz).length ? 'Finish game' : 'Next question'} <i data-lucide="arrow-right"></i></button><button class="btn btn-secondary" data-action="couple-back">Exit room</button></div>` : ''}<div class="form-help" style="margin-top:18px">${answered ? 'Your answer is saved to the room while you wait.' : `Responding as ${escapeHtml(myRole)}.`} Room state is synced through Firestore.</div></section>`;
  }

  function createCoupleRoom(gameId) {
    if (!coupleGameInfo[gameId]) return;
    const code = Math.random().toString(36).slice(2,8).toUpperCase();
    const room = { id: uid('couple'), code, gameId, ownerId: currentUserId, partnerId: '', index: 0, responses: {}, answerCreatedAt: {}, answeredBy: {}, createdAt: now(), expiresAt: now() + 24 * 60 * 60 * 1000 };
    db.coupleRooms.push(room);
    activeCoupleRoomId = room.id;
    persist();
    setPage('couples');
    toast(`Private room created. Share code ${code} with your partner.`);
  }

  function openJoinCoupleRoomModal() {
    showModal(`<span class="eyebrow">JOIN YOUR PERSON</span><h2 id="modalTitle" class="modal-content-title">Enter a room code.</h2><p class="modal-subtitle">Join a private two-player session with the six-character code shared by your partner.</p><form id="joinCoupleRoomForm" class="settings-form"><label>Room code<input class="field" name="code" maxlength="6" minlength="6" autocomplete="off" placeholder="ABC123" required></label><div class="modal-actions"><button type="button" class="btn btn-quiet" data-action="close-modal">Cancel</button><button type="submit" class="btn btn-primary">Join room <i data-lucide="arrow-up-right"></i></button></div></form><p class="form-help">Room membership and answers sync through Firestore. Avoid sharing private information you would not want the other room participant to retain.</p>`);
  }

  function renderChats() {
    const gcs = myGcs();
    const otherUsers = Object.values(db.users).filter(user => user.id !== currentUserId).sort((a,b) => a.name.localeCompare(b.name));
    if (chatTargetType === 'gc' && !gcs.some(gc => gc.id === chatTargetId)) chatTargetId = gcs[0]?.id || '';
    if (chatTargetType === 'dm' && !otherUsers.some(user => user.id === chatTargetId)) { chatTargetType = 'gc'; chatTargetId = gcs[0]?.id || ''; }
    const selectedGc = chatTargetType === 'gc' ? getGc(chatTargetId) : null;
    const selectedUser = chatTargetType === 'dm' ? db.users[chatTargetId] : null;
    let messages = [];
    if (selectedGc) messages = db.messages.filter(message => message.type === 'gc' && message.gcId === selectedGc.id);
    if (selectedUser) messages = db.messages.filter(message => message.type === 'dm' && [message.fromId, message.toId].includes(currentUserId) && [message.fromId, message.toId].includes(selectedUser.id));
    const hiddenMessageIds = prefsFor().hiddenMessages || [];
    messages = messages.filter(message => message.expiresAt > now() && !hiddenMessageIds.includes(message.id)).sort((a,b) => a.createdAt - b.createdAt);
    const targetName = selectedGc ? `${selectedGc.emoji || '🔥'} ${selectedGc.name}` : selectedUser ? selectedUser.name : 'Select a conversation';
    const gcRows = gcs.map(gc => `<button class="side-link ${selectedGc?.id === gc.id ? 'active' : ''}" style="width:100%;margin-top:5px" data-action="chat-select-gc" data-id="${gc.id}"><span style="font-size:17px">${escapeHtml(gc.emoji || '🔥')}</span><span style="overflow:hidden;text-overflow:ellipsis;white-space:nowrap">${escapeHtml(gc.name)}</span></button>`).join('') || '<p class="small muted">Create or join a GC to start group chats.</p>';
    const dmRows = otherUsers.map(user => `<button class="side-link chat-user-row ${selectedUser?.id === user.id ? 'active' : ''}" style="width:100%;margin-top:5px" data-action="chat-select-dm" data-id="${user.id}" data-user-search="${escapeHtml(`${user.name} @${user.username || ''} ${user.email || ''}`.toLowerCase())}"><span class="avatar avatar-small">${escapeHtml(initials(user.name))}</span><span style="display:grid;min-width:0;text-align:left;overflow:hidden"><b style="overflow:hidden;text-overflow:ellipsis;white-space:nowrap">${escapeHtml(user.name)}</b><small style="color:var(--muted);font-weight:400">@${escapeHtml(user.username || 'player')}</small></span></button>`).join('') || '<p class="small muted">No other GCVERSE members found. Share your username so a friend can join.</p>';
    const bubbles = messages.map(message => { const own = message.fromId === currentUserId; return `<div style="display:flex;justify-content:${own ? 'flex-end' : 'flex-start'};margin:10px 0"><div style="max-width:min(82%,560px);padding:11px 13px;border:1px solid ${own ? 'rgba(167,139,250,.25)' : 'var(--line)'};background:${own ? 'rgba(130,96,225,.16)' : 'rgba(255,255,255,.035)'};border-radius:${own ? '14px 14px 4px 14px' : '14px 14px 14px 4px'}"><div style="font-size:10px;color:var(--muted);margin-bottom:5px">${escapeHtml(db.users[message.fromId]?.name || 'Member')} · ${ago(message.createdAt)} · expires in ${Math.max(1, Math.ceil((message.expiresAt-now())/60000))}m</div><div style="white-space:pre-wrap;overflow-wrap:anywhere">${escapeHtml(message.text)}</div></div></div>`; }).join('');
    return `<div class="page-intro"><div><span class="eyebrow"><span class="pulse-dot"></span> TALK HERE. IT FADES LATER.</span><h1>Chats. 💬</h1><p>GC group chats and direct messages with text and emoji. Messages are hidden after 10 minutes and removed asynchronously when Firestore TTL runs.</p></div><div class="page-actions"><span class="pill purple">10 MINUTE MESSAGES</span></div></div>
      <div style="display:grid;grid-template-columns:minmax(190px,260px) minmax(0,1fr);gap:16px;align-items:start" class="chat-layout"><aside class="card settings-card" style="padding:15px"><div class="section-head"><h3>Group chats</h3><span class="pill">${gcs.length}</span></div>${gcRows}<div class="nav-divider"></div><div class="section-head"><h3>Direct messages</h3><span class="pill">${otherUsers.length}</span></div><input id="chatUserSearch" class="field" type="search" placeholder="Search name or @username" aria-label="Search users" style="margin:8px 0">${dmRows}<p class="form-help" style="margin-top:14px">Messages sync live across signed-in devices and expire after 10 minutes.</p></aside>
      <section class="card" style="min-height:520px;padding:0;overflow:hidden;display:flex;flex-direction:column"><div style="padding:17px 18px;border-bottom:1px solid var(--line);display:flex;justify-content:space-between;align-items:center;gap:10px"><div><span class="section-kicker">${selectedGc ? 'GROUP CONVERSATION' : selectedUser ? 'DIRECT MESSAGE' : 'CONVERSATION'}</span><h2 style="font-size:19px;margin:5px 0 0">${escapeHtml(targetName)}</h2>${selectedGc ? `<p class="muted small" style="margin-top:5px">${selectedGc.members.length} group members</p>` : ''}</div>${(selectedGc || selectedUser) ? `<button class="icon-button" data-action="clear-chat" title="Clear this local conversation"><i data-lucide="trash-2"></i></button>` : ''}</div>
      <div style="padding:12px 18px;flex:1;min-height:270px;max-height:52vh;overflow:auto" id="chatMessages">${messages.length ? bubbles : `<div class="empty-state"><div class="empty-icon">💬</div><h3>No messages yet</h3><p>Start with a hello. Messages are hidden after 10 minutes.</p></div>`}</div>
      ${(selectedGc || selectedUser) ? `<form id="chatMessageForm" style="padding:13px;border-top:1px solid var(--line);display:flex;gap:9px;align-items:flex-end"><input type="hidden" name="type" value="${selectedGc ? 'gc' : 'dm'}"><input type="hidden" name="gcId" value="${selectedGc ? selectedGc.id : ''}"><input type="hidden" name="recipientId" value="${selectedUser ? selectedUser.id : ''}"><textarea name="message" class="textarea-field" rows="2" maxlength="1000" required placeholder="Write a message… emoji welcome 🙂" style="min-height:55px;resize:vertical;flex:1"></textarea><button class="btn btn-primary" type="submit" style="min-height:43px"><i data-lucide="send"></i> Send</button></form>` : '<div class="empty-state"><p>Create or join a GC, or select a direct message.</p><button class="btn btn-primary" data-action="create-gc">Create GC</button></div>'}</section></div>
      <style>@media(max-width:760px){.chat-layout{grid-template-columns:1fr!important}.chat-layout>aside{max-height:240px;overflow:auto}.chat-layout>section{min-height:460px!important}}</style>`;
  }

  function saveCoupleAnswer(answer) {
    const room = coupleRoom();
    if (!room) return toast('Couple room not found.', 'error');
    if (!room.partnerId) return toast('Ask your partner to join this room first.', 'error');
    if (room.ownerId !== currentUserId && room.partnerId !== currentUserId) return toast('You are not a member of this room.', 'error');
    room.responses ||= {};
    room.responses[room.index] ||= {};
    if (room.responses[room.index][currentUserId] !== undefined) return toast('Your answer is already locked.', 'error');
    room.responses[room.index][currentUserId] = String(answer).trim();
    room.answerCreatedAt ||= {};
    room.answerCreatedAt[String(room.index)] ||= {};
    room.answerCreatedAt[String(room.index)][currentUserId] = now();
    room.answeredBy ||= {};
    room.answeredBy[String(room.index)] = [...new Set([...(room.answeredBy[String(room.index)] || []), currentUserId])];
    persist();
    renderPage();
    const submitted = room.answeredBy?.[String(room.index)] || [];
    const bothSubmitted = Boolean(room.partnerId && submitted.includes(room.ownerId) && submitted.includes(room.partnerId));
    if (bothSubmitted) {
      toast('Both answers are in. Reveal time!');
      void hydrateCoupleRoomResponses(room).then(() => { if (page === 'couples') renderPage(); });
    } else toast('Answer locked. Your partner’s answer stays hidden until they respond.');
  }

  function renderPage() {
    if (!currentUser()) return;
    const node = $('#pageView');
    const pages = { home: renderHome, games: renderGames, couples: renderCouples, chats: renderChats, confessions: renderConfessions, leaderboard: renderLeaderboard, profile: renderProfile, gc: renderGcOverview, game: renderGame };
    node.innerHTML = (pages[page] || renderHome)();
    refreshIcons();
  }

  /* Game flow */
  function startGame(gameId) {
    if (!gameInfo[gameId]) return;
    if (['truth', 'redflag', 'challenge', 'tmkoc'].includes(gameId) && !getGc(selectedGcId)) {
      setPage('games');
      toast('Choose a GC first, then launch this game.');
      return;
    }
    if (gameId === 'xo') {
      game = { id: 'xo', stage: 'xo-mode', xp: 0 };
    } else if (gameId === 'puzzle') {
      game = { id: 'puzzle', stage: 'puzzle', questions: shuffle(puzzleQuestions).slice(0, 10), index: 0, score: 0, streak: 0, bestStreak: 0, answered: false, xp: 0 };
    } else if (gameId === 'truth') {
      game = { id: gameId, stage: 'td-setup', gcId: selectedGcId, round: 1, players: [], usedTruth: [], usedDare: [], choices: {}, assignments: [], index: 0, xp: 0 };
    } else if (gameId === 'redflag') {
      game = { id: gameId, stage: 'redflag', gcId: selectedGcId, questions: shuffle(redFlagScenarios).slice(0, 12), index: 0, answers: [], xp: 0, mode: 'solo' };
    } else if (gameId === 'challenge') {
      game = { id: gameId, stage: 'challenge', gcId: selectedGcId, round: 1, rounds: [], used: [], rerollUsed: false, done: false, xp: 0 };
      assignChallengeRound();
    } else if (gameId === 'tmkoc') {
      const gc = getGc(selectedGcId);
      if (gc.members.length > 10) toast('This match has 10 character slots. Choose up to 10 participants.', 'error');
      game = { id: gameId, stage: 'tmkoc-lobby', gcId: selectedGcId, players: [currentUserId], activePlayerIndex: 0, playerResults: [], assignments: [], questions: tmkocQuestions, index: 0, scores: { chaos: 0, drama: 0, confidence: 0, loyalty: 0, logic: 0 }, answers: [], xp: 0 };
    }
    page = 'game';
    renderSidebar();
    renderPage();
    window.scrollTo({ top: 0, behavior: 'smooth' });
  }
  function finishGame(xp, summary, win = false) {
    if (!game || game.completed) return;
    game.completed = true;
    game.xp = xp;
    const stats = statsFor();
    stats.xp += xp;
    stats.gamesPlayed += 1;
    if (win) stats.wins += 1;
    if (game.id === 'puzzle' && game.score > (stats.bestPuzzle || 0)) stats.bestPuzzle = game.score;
    const gc = game.gcId ? getGc(game.gcId) : null;
    if (gc) {
      gc.gamesPlayed = (gc.gamesPlayed || 0) + 1;
      gc.lastPlayedAt = now();
      const member = memberFor(gc);
      if (member) { member.xp = (member.xp || 0) + xp; member.gamesPlayed = (member.gamesPlayed || 0) + 1; if (win) member.wins = (member.wins || 0) + 1; }
    }
    db.gameSessions.push({ id: uid('session'), userId: currentUserId, gcId: game.gcId || null, gcName: gc?.name || '', gameId: game.id, xp, win, summary, createdAt: now(), expiresAt: now() + 7 * 24 * 60 * 60 * 1000 });
    persist();
    game.stage = 'result';
    game.result = { xp, summary, win };
    renderPage();
  }
  function resultPanel() {
    const g = game;
    const result = g.result || { xp: g.xp || 0, summary: 'Round completed.', win: false };
    return `<section class="stage-panel"><div class="stage-question"><span class="big-emoji">${result.win ? '🏆' : '✨'}</span><span class="eyebrow">SESSION COMPLETE</span><h2>${result.win ? 'You got the win.' : 'That is a wrap.'}</h2><p>${escapeHtml(result.summary)}</p><div class="tally-grid"><div class="tally"><strong>+${result.xp}</strong><span>XP earned</span></div><div class="tally"><strong>${statsFor().gamesPlayed}</strong><span>Games played</span></div><div class="tally"><strong>${statsFor().xp.toLocaleString()}</strong><span>Total XP</span></div></div><div class="stage-actions"><button class="btn btn-primary" data-action="replay-game">Play again <i data-lucide="rotate-ccw"></i></button><button class="btn btn-secondary" data-action="back-to-games">Back to games</button><button class="btn btn-quiet" data-action="share-result"><i data-lucide="copy"></i> Copy result</button></div></div></section>`;
  }
  function renderGame() {
    if (!game) { page = 'games'; return renderGames(); }
    if (game.stage === 'result') return `<div class="game-room-header"><button class="back-link" data-action="back-to-games"><i data-lucide="arrow-left"></i> Back to games</button><div class="room-header-copy"><span class="eyebrow">GAME COMPLETE</span><h1>${gameInfo[game.id].title}</h1><p>Stats stay on your profile. Detailed game session expires after seven days.</p></div></div><div class="game-stage">${resultPanel()}</div>`;
    const header = `<div class="game-room-header"><button class="back-link" data-action="back-to-games"><i data-lucide="arrow-left"></i> Exit game</button><span class="gc-emblem">${gameInfo[game.id].icon}</span><div class="room-header-copy"><span class="eyebrow">${escapeHtml(gameInfo[game.id].tag)}</span><h1>${gameInfo[game.id].title}</h1><p>${escapeHtml(game.gcId ? getGc(game.gcId)?.name || 'Your GC' : 'Solo mode')} · XP and result history sync to Firestore; round flow runs in this browser</p></div><span class="pill purple">LOCAL SESSION</span></div>`;
    return `${header}<div class="game-stage">${renderGameStage()}</div>`;
  }
  function renderGameStage() {
    switch (game.id) {
      case 'truth': return renderTruthGame();
      case 'redflag': return renderRedFlagGame();
      case 'challenge': return renderChallengeGame();
      case 'tmkoc': return renderTMKOCGame();
      case 'xo': return renderXOGame();
      case 'puzzle': return renderPuzzleGame();
      default: return '<div class="empty-state">Game not found.</div>';
    }
  }
  function renderTruthGame() {
    const gc = getGc(game.gcId);
    const members = (gc?.members || []).slice(0, 15);
    if (game.stage === 'td-setup') {
      return `<section class="stage-panel"><div class="stage-topline"><span class="pill purple">ROUND ${game.round} / 3</span><span class="pill">EXACTLY 2 PLAYERS</span></div><div class="stage-question"><span class="big-emoji">🎭</span><h2>Choose your two players.</h2><p>Both players choose a preference before their prompts are revealed. Truth, Dare, Random or a custom prompt.</p></div><div class="modal-member-list">${members.map(member => `<label class="modal-member-row"><input type="checkbox" data-player-select="${member.userId}" ${game.players.includes(member.userId) ? 'checked' : ''} ${game.players.length >= 2 && !game.players.includes(member.userId) ? 'disabled' : ''}><span class="avatar">${escapeHtml(initials(member.name))}</span><span>${escapeHtml(member.name)}${member.userId === currentUserId ? ' (you)' : ''}</span><small>${member.role === 'owner' ? 'Owner' : member.preview ? 'Preview member' : 'Member'}</small></label>`).join('')}</div>${members.length < 2 ? '<div class="confession-note" style="margin-top:15px"><strong>🧪 Solo preview</strong><p>Your GC currently has fewer than two members. Try a sample guest here; in real multiplayer, invite a second player with the GC code.</p></div>' : ''}<div class="stage-actions"><button class="btn btn-secondary" data-action="td-demo">Try with sample guest</button><button class="btn btn-primary" data-action="td-preferences" ${game.players.length !== 2 ? 'disabled' : ''}>Lock players & continue <i data-lucide="arrow-right"></i></button></div></section>`;
    }
    if (game.stage === 'td-preferences') {
      const selected = game.players.map(id => members.find(member => member.userId === id) || game.guestPlayers?.find(member => member.userId === id)).filter(Boolean);
      return `<section class="stage-panel"><div class="stage-topline"><span class="pill purple">ROUND ${game.round} / 3</span><span class="pill">PREFERENCES ARE PRIVATE IN THE CONNECTED VERSION</span></div><div class="stage-question"><span class="big-emoji">🔒</span><h2>Lock your preference.</h2><p>This setup currently runs on one device. Private per-player choices need a dedicated shared game-session workflow.</p></div>${selected.map((member, index) => `<div class="card" style="padding:17px;margin-top:12px"><div style="display:flex;align-items:center;gap:9px;margin-bottom:12px">${initialsAvatar(member.name)}<div><strong style="font-size:12px">${escapeHtml(member.name)}</strong><div class="small muted">Player ${index + 1}</div></div></div><div class="choice-pills">${[['truth','🟢 Truth'],['dare','🔴 Dare'],['random','🎲 Random'],['manual','✍️ Custom']].map(([value,label]) => `<button class="choice-pill ${game.choices[member.userId]?.preference === value ? 'active' : ''}" data-action="td-choice" data-player="${member.userId}" data-pref="${value}">${label}</button>`).join('')}</div><textarea class="textarea-field" style="margin-top:11px;min-height:68px" data-td-custom="${member.userId}" placeholder="Optional custom truth or dare...">${escapeHtml(game.choices[member.userId]?.custom || '')}</textarea></div>`).join('')}<div class="stage-actions"><button class="btn btn-secondary" data-action="td-back">Back</button><button class="btn btn-primary" data-action="td-reveal" ${selected.some(member => !game.choices[member.userId]?.preference) ? 'disabled' : ''}>Reveal prompts <i data-lucide="sparkles"></i></button></div></section>`;
    }
    if (game.stage === 'td-reveal') {
      const assignment = game.assignments[game.index];
      return `<section class="stage-panel"><div class="stage-topline"><span class="pill purple">ROUND ${game.round} / 3</span><span class="pill">PLAYER ${game.index + 1} OF 2</span></div><div class="stage-question"><span class="big-emoji">${assignment?.type === 'Truth' ? '🟢' : '🔴'}</span><span class="eyebrow">${escapeHtml(assignment?.playerName || 'Player')}'S TURN</span><h2>${assignment?.type === 'Truth' ? 'Truth time.' : 'Dare accepted?'}</h2><p>Only the current player should read this prompt in a real session. Complete it before passing the device.</p></div><div class="challenge-prompt-card" style="min-height:0;margin-top:20px"><span class="pill ${assignment?.type === 'Truth' ? 'mint' : 'red'}">${assignment?.type?.toUpperCase() || 'PROMPT'}</span><h2>${escapeHtml(assignment?.prompt || '')}</h2><p>${assignment?.custom ? 'Player-submitted custom prompt' : 'Choose honesty, keep it respectful, and pass on anything that feels uncomfortable.'}</p><div class="stage-actions"><button class="btn btn-primary" data-action="td-next">${game.index === 0 ? 'Mark done · Next player' : (game.round < 3 ? 'Round complete · Next round' : 'Finish game')} <i data-lucide="arrow-right"></i></button></div></div></section>`;
    }
    return '<div class="empty-state">Setting up Truth & Dare…</div>';
  }
  function getTruthDareAssignment(player, index) {
    const choice = game.choices[player.userId] || { preference: 'random', custom: '' };
    const manualPrompt = choice.custom?.trim() || '';
    const type = choice.preference === 'random' || (choice.preference === 'manual' && !manualPrompt) ? (Math.random() < .5 ? 'Truth' : 'Dare') : choice.preference === 'truth' ? 'Truth' : choice.preference === 'dare' ? 'Dare' : 'Custom';
    if (choice.preference === 'manual' && manualPrompt) return { playerId: player.userId, playerName: player.name, type: 'Custom', prompt: manualPrompt, custom: true };
    const isTruth = type === 'Truth';
    const pool = isTruth ? truthPrompts : darePrompts;
    const used = isTruth ? game.usedTruth : game.usedDare;
    const available = pool.filter(prompt => !used.includes(prompt));
    const prompt = pick(available.length ? available : pool);
    used.push(prompt);
    return { playerId: player.userId, playerName: player.name, type, prompt, custom: false };
  }
  function assignChallengeRound() {
    const gc = getGc(game.gcId);
    let members = (gc?.members || []).slice(0, 15);
    if (members.length < 2) members = [...members, { userId: `${currentUserId}_guest`, name: 'Sample Guest', role: 'member', preview: true, xp: 0 }];
    const available = challengePrompts.filter(item => !game.used.includes(item.id));
    const selected = shuffle(available).slice(0, members.length);
    if (!selected.length) return;
    selected.forEach(item => game.used.push(item.id));
    game.rounds[game.round - 1] = members.map((member, index) => ({ userId: member.userId, name: member.name, challenge: selected[index % selected.length], done: false }));
  }
  function renderChallengeGame() {
    const gc = getGc(game.gcId);
    const assignments = game.rounds[game.round - 1] || [];
    const own = assignments.find(item => item.userId === currentUserId) || assignments[0];
    const doneCount = assignments.filter(item => item.done).length;
    const challenge = own?.challenge;
    const difficulty = challenge?.difficulty || 'medium';
    const difficultyLabel = difficulty === 'hard' ? 'HARD' : difficulty === 'medium' ? 'MEDIUM' : 'EASY';
    return `<section class="stage-panel"><div class="stage-topline"><span class="pill orange">ROUND ${game.round} / 4</span><div class="round-dots">${[1,2,3,4].map(n => `<span class="round-dot ${n < game.round ? 'done' : n === game.round ? 'current' : ''}"></span>`).join('')}</div><span class="pill">${assignments.length} players</span></div><div class="stage-progress"><span style="width:${(game.round - 1) / 4 * 100 + (game.done ? 100 : 0)}%"></span></div><div class="round-challenge-layout"><div class="challenge-prompt-card"><span class="prompt-emoji">🎲</span><span class="pill ${difficulty === 'hard' ? 'red' : difficulty === 'medium' ? 'orange' : 'mint'}">${difficultyLabel} · ${escapeHtml(challenge?.category || 'challenge').toUpperCase()}</span><h2>${escapeHtml(challenge?.text || 'Your challenge is loading…')}</h2><p>Your assignment is unique for this match. The other players have different prompts. Complete a challenge only if it feels safe and comfortable.</p><div class="stage-actions" style="justify-content:flex-start"><button class="btn btn-primary" data-action="challenge-done" ${own?.done ? 'disabled' : ''}>${own?.done ? 'Completed ✓' : 'I completed it ✓'}</button><button class="btn btn-secondary" data-action="challenge-reroll" ${game.rerollUsed || own?.done ? 'disabled' : ''}><i data-lucide="refresh-cw"></i> Re-roll once</button></div></div><aside class="challenge-roster"><span class="section-kicker">ROUND PROGRESS</span><h3>Players</h3><p>${doneCount} of ${assignments.length} marked complete in this game instance.</p>${assignments.map(item => `<div class="roster-row">${initialsAvatar(item.name)}<span>${escapeHtml(item.name)}${item.userId === currentUserId ? ' (you)' : ''}</span><span class="done-mark">${item.done ? '✓' : '…'}</span></div>`).join('')}<div class="stage-progress"><span style="width:${assignments.length ? doneCount / assignments.length * 100 : 0}%"></span></div><p class="small muted">${challengePrompts.length} unique challenge prompts in the deck.</p></aside></div><div class="stage-actions"><button class="btn btn-quiet" data-action="challenge-next" ${!own?.done ? 'disabled' : ''}>${game.round < 4 ? 'Next round →' : 'Finish challenge'}</button></div></section>`;
  }
  function renderRedFlagGame() {
    const total = game.questions.length;
    if (game.index >= total) {
      const counts = { red: 0, depends: 0, green: 0 };
      game.answers.forEach(answer => counts[answer.value]++);
      const score = Math.round((counts.red + counts.depends * .5) / total * 100);
      game.redScore = score;
      const label = score >= 70 ? 'The Boundary Enforcer' : score >= 45 ? 'The Context Detective' : 'The Optimist';
      return `<section class="stage-panel"><div class="stage-question"><span class="big-emoji">🚩</span><span class="eyebrow">YOUR VERDICT PROFILE</span><h2>${label}</h2><p>You rated ${counts.red} situations as red flags, ${counts.depends} as context-dependent, and ${counts.green} as green. These are your opinions, not a clinical or expert diagnosis.</p></div><div class="scenario-result"><strong style="font-size:12px">Your answers</strong><div class="result-bars">${[['Red flag',counts.red,'#ff818c'],['Depends',counts.depends,'#ffc27a'],['Green flag',counts.green,'#87e7b5']].map(([label,count,color]) => `<div><div class="result-bar-label"><span>${label}</span><b>${Math.round(count / total * 100)}%</b></div><div class="result-bar"><span style="width:${count / total * 100}%;background:${color}"></span></div></div>`).join('')}</div></div><div class="stage-actions"><button class="btn btn-primary" data-action="redflag-finish">Save result · +80 XP</button><button class="btn btn-secondary" data-action="replay-game">Play again</button></div></section>`;
    }
    const item = game.questions[game.index];
    const progress = game.index / total * 100;
    return `<section class="stage-panel"><div class="stage-topline"><span class="pill red">SITUATION ${String(game.index + 1).padStart(2,'0')} / ${total}</span><span class="pill">${escapeHtml(item.area.toUpperCase())}</span></div><div class="stage-progress"><span style="width:${progress}%"></span></div><div class="scenario-card"><span class="scenario-number">RELATIONSHIP CASE FILE · ${String(game.index + 1).padStart(2,'0')}</span><h2>${escapeHtml(item.text)}</h2><p class="scenario-context">Focus on the behaviour, boundaries and context—not assumptions about someone's entire character.</p></div><div class="choice-grid"><button class="choice-card green" data-action="redflag-answer" data-value="green"><span class="choice-emoji">🟢</span><strong>Not a red flag</strong><small>Seems okay</small></button><button class="choice-card yellow" data-action="redflag-answer" data-value="depends"><span class="choice-emoji">🟡</span><strong>It depends</strong><small>Needs context</small></button><button class="choice-card red" data-action="redflag-answer" data-value="red"><span class="choice-emoji">🚩</span><strong>Red flag</strong><small>Could be unhealthy</small></button></div><p class="small muted" style="text-align:center;margin:15px 0 0">Scenario ${game.index + 1} of ${total} · Individual votes are not yet synchronized between devices.</p></section>`;
  }
  function renderTMKOCGame() {
    const gc = getGc(game.gcId);
    const members = (gc?.members || []).slice(0, 10);
    if (game.stage === 'tmkoc-lobby') {
      return `<section class="stage-panel"><div class="stage-topline"><span class="pill orange">GROUP CAST</span><span class="pill">${game.players.length} / 10 SLOTS</span></div><div class="stage-question"><span class="big-emoji">🇮🇳</span><h2>Who is joining the cast?</h2><p>Choose up to 10 people from this GC. Each participant gets one unique character. Character assignment currently runs on this device; per-player cross-device game turns need a shared game-session workflow.</p></div><div class="modal-member-list">${members.map(member => `<label class="modal-member-row"><input type="checkbox" data-tmkoc-select="${member.userId}" ${game.players.includes(member.userId) ? 'checked' : ''} ${game.players.length >= 10 && !game.players.includes(member.userId) ? 'disabled' : ''}><span class="avatar">${escapeHtml(initials(member.name))}</span><span>${escapeHtml(member.name)}${member.userId === currentUserId ? ' (you)' : ''}</span><small>${member.role === 'owner' ? 'Owner' : member.preview ? 'Preview' : 'Member'}</small></label>`).join('')}</div>${members.length > 10 ? '<p class="form-help">Only the first 10 GC members are available in this preview. Character slots are limited to 10.</p>' : ''}<div class="stage-actions"><button class="btn btn-secondary" data-action="back-to-games">Cancel</button><button class="btn btn-primary" data-action="tmkoc-start" ${game.players.length < 1 ? 'disabled' : ''}>Start personality scan <i data-lucide="arrow-right"></i></button></div></section>`;
    }
    if (game.stage === 'tmkoc-pass') {
      const nextPlayer = findPlayerForGame(game.players[game.activePlayerIndex + 1]);
      const completed = game.playerResults.length;
      return `<section class="stage-panel"><div class="stage-question"><span class="big-emoji">🔄</span><span class="eyebrow">PLAYER ${completed + 1} OF ${game.players.length}</span><h2>Pass the device to ${escapeHtml(nextPlayer?.name || 'the next player')}.</h2><p>Keep previous answers private. In the connected version, each player will see and submit their quiz on their own device.</p><div class="stage-actions"><button class="btn btn-primary" data-action="tmkoc-next-player">${escapeHtml(nextPlayer?.name || 'Next player')}, I'm ready <i data-lucide="arrow-right"></i></button></div></div></section>`;
    }
    if (game.stage === 'tmkoc-group-result') {
      const meResult = game.assignments.find(item => item.userId === currentUserId) || game.assignments[0];
      const character = meResult?.character || tmkocCharacters[0];
      const traits = Object.entries(character.traits);
      return `<section class="stage-panel"><div class="tmkoc-result"><span class="eyebrow">🇮🇳 YOUR TMKOC CHARACTER</span><span class="character-emoji">${character.emoji}</span><h2 class="character-name">${escapeHtml(character.name)}</h2><p class="character-quote">“${escapeHtml(character.quote)}”</p><div class="trait-list">${traits.map(([trait,value]) => `<div class="trait-line"><span>${trait.charAt(0).toUpperCase() + trait.slice(1)}</span><div class="result-bar"><span style="width:${value}%;background:${trait === 'chaos' ? '#f5a7d4' : trait === 'loyalty' ? '#8be6c3' : '#a78bfa'}"></span></div><strong>${value}%</strong></div>`).join('')}</div><div class="pill orange">${game.assignments.length} UNIQUE CHARACTER${game.assignments.length === 1 ? '' : 'S'} ASSIGNED</div></div><div class="section-head" style="margin-top:25px"><div><span class="section-kicker">YOUR GC CAST</span><h2>Gokuldham, assembled.</h2></div><span class="pill mint">No duplicates</span></div><div class="character-cast-grid">${game.assignments.map(item => `<div class="cast-tile"><span class="cast-emoji">${item.character.emoji}</span><strong>${escapeHtml(item.character.name)}</strong><span>${escapeHtml(item.name)}${item.userId === currentUserId ? ' · you' : ''}</span></div>`).join('')}</div><p class="small muted" style="margin-top:14px">Character assignments are unique within this match. In online multiplayer, each person will submit their own answers before the group reveal.</p><div class="stage-actions"><button class="btn btn-primary" data-action="tmkoc-finish">Save cast · +60 XP</button><button class="btn btn-secondary" data-action="tmkoc-restart">Run it again</button></div></section>`;
    }
    const item = game.questions[game.index];
    const player = findPlayerForGame(game.players[game.activePlayerIndex]) || currentUser();
    return `<section class="stage-panel"><div class="stage-topline"><span class="pill orange">PERSONALITY SCAN</span><span class="pill">PLAYER ${game.activePlayerIndex + 1} / ${game.players.length}</span><span class="pill">QUESTION ${game.index + 1} / ${game.questions.length}</span></div><div class="stage-progress"><span style="width:${game.index / game.questions.length * 100}%"></span></div><div class="stage-question"><span class="big-emoji">🇮🇳</span><span class="eyebrow">${escapeHtml(player?.name || 'Player')}'S TURN</span><h2>${escapeHtml(item.q)}</h2><p>Choose the answer that feels most like you—not the character you want to get.</p></div><div class="choice-grid" style="grid-template-columns:repeat(2,minmax(0,1fr))">${item.options.map((option,index) => `<button class="choice-card" data-action="tmkoc-answer" data-option="${index}" style="min-height:106px"><span class="choice-emoji">${['⚡','🧠','❤️','🎭'][index]}</span><strong>${escapeHtml(option.t)}</strong></button>`).join('')}</div></section>`;
  }

  function assignUniqueTMKOCCharacters(playerResults) {
    const pool = [...tmkocCharacters];
    const pairs = [];
    playerResults.forEach((result, playerIndex) => {
      const total = Object.values(result.scores).reduce((sum, value) => sum + value, 0) || 1;
      pool.forEach((character, characterIndex) => {
        const fit = Object.entries(result.scores).reduce((sum, [trait, score]) => sum + (character.traits[trait] || 50) * (score / total), 0);
        pairs.push({ playerIndex, characterIndex, score: fit + Math.random() * 3 });
      });
    });
    pairs.sort((a, b) => b.score - a.score);
    const assignedPlayers = new Set();
    const assignedCharacters = new Set();
    const results = [];
    for (const pair of pairs) {
      if (assignedPlayers.has(pair.playerIndex) || assignedCharacters.has(pair.characterIndex)) continue;
      assignedPlayers.add(pair.playerIndex); assignedCharacters.add(pair.characterIndex);
      results.push({ ...playerResults[pair.playerIndex], character: pool[pair.characterIndex] });
      if (assignedPlayers.size === playerResults.length) break;
    }
    // A deterministic fallback guarantees every participant receives a unique slot.
    playerResults.forEach((result, index) => {
      if (!assignedPlayers.has(index)) {
        const character = pool.find(item => !assignedCharacters.has(pool.indexOf(item))) || pool[index];
        const characterIndex = pool.indexOf(character);
        assignedCharacters.add(characterIndex); assignedPlayers.add(index);
        results.push({ ...result, character });
      }
    });
    return results.sort((a, b) => playerResults.findIndex(item => item.userId === a.userId) - playerResults.findIndex(item => item.userId === b.userId));
  }
  function renderXOGame() {
    if (game.stage === 'xo-mode') return `<section class="stage-panel"><div class="stage-question"><span class="big-emoji">❌⭕</span><h2>Choose your opponent.</h2><p>Play a quick strategy match. Computer mode works locally; invite-link multiplayer will be connected with Firebase later.</p></div><div class="choice-grid" style="max-width:600px;margin-left:auto;margin-right:auto"><button class="choice-card" data-action="xo-start" data-mode="computer"><span class="choice-emoji">🤖</span><strong>Play vs computer</strong><small>Easy · Medium · Hard</small></button><button class="choice-card" data-action="xo-start" data-mode="local"><span class="choice-emoji">👥</span><strong>Two players here</strong><small>Pass the device</small></button></div><div class="stage-actions"><button class="btn btn-quiet" data-action="back-to-games">Back to games</button></div></section>`;
    const board = game.board || Array(9).fill('');
    const winning = game.winning || [];
    const status = game.finished ? (game.winner === 'X' ? 'You win! 🎉' : game.winner === 'O' ? (game.mode === 'computer' ? 'Computer wins this one.' : 'Player O wins!') : 'It is a draw.') : game.mode === 'computer' ? (game.turn === 'X' ? 'Your turn · X' : 'Computer thinking · O') : `Player ${game.turn} to move`;
    return `<section class="stage-panel"><div class="stage-topline"><span class="pill mint">${game.mode === 'computer' ? `VS COMPUTER · ${String(game.difficulty || 'hard').toUpperCase()}` : 'LOCAL 2 PLAYER'}</span><button class="btn btn-quiet" data-action="xo-reset">Restart</button></div><div class="xo-layout"><div class="xo-players"><div class="xo-player ${game.turn === 'X' && !game.finished ? 'active' : ''}">${initialsAvatar(currentUser()?.name || 'You')}<span class="xo-player-meta"><strong>${escapeHtml(currentUser()?.name || 'You')} · X</strong><small>${game.mode === 'computer' ? 'You' : 'Player X'}</small></span></div><span class="xo-vs">VS</span><div class="xo-player ${game.turn === 'O' && !game.finished ? 'active' : ''}">${initialsAvatar(game.mode === 'computer' ? 'AI' : 'Friend')}<span class="xo-player-meta"><strong>${game.mode === 'computer' ? 'GC Bot' : 'Friend'} · O</strong><small>${game.mode === 'computer' ? 'Computer' : 'Player O'}</small></span></div></div><div class="xo-board">${board.map((cell,index) => `<button class="xo-cell ${cell === 'X' ? 'x' : cell === 'O' ? 'o' : ''}" data-action="xo-move" data-index="${index}" ${cell || game.finished || (game.mode === 'computer' && game.turn === 'O') ? 'disabled' : ''}>${cell}${winning.includes(index) ? ' ✦' : ''}</button>`).join('')}</div><div class="xo-status">${status}</div>${game.finished ? `<div class="stage-actions"><button class="btn btn-primary" data-action="xo-finish">Save match · +${game.winner === 'X' ? 50 : 15} XP</button><button class="btn btn-secondary" data-action="xo-reset">Play again</button></div>` : ''}</div></section>`;
  }
  function renderPuzzleGame() {
    if (game.stage === 'puzzle-result') return `<section class="stage-panel"><div class="stage-question"><span class="big-emoji">🧩</span><span class="eyebrow">PUZZLE RUN COMPLETE</span><h2>${game.score} / ${game.questions.length} correct</h2><p>${game.score >= 9 ? 'Puzzle Master energy.' : game.score >= 6 ? 'Nice run. Your pattern recognition is improving.' : 'Good warm-up. Try another run and beat your score.'}</p><div class="tally-grid"><div class="tally"><strong>${game.score * 10}</strong><span>Score</span></div><div class="tally"><strong>${game.bestStreak || 0}</strong><span>Best streak</span></div><div class="tally"><strong>${statsFor().bestPuzzle || 0}</strong><span>Best run</span></div></div><div class="stage-actions"><button class="btn btn-primary" data-action="replay-game">Run it back</button><button class="btn btn-secondary" data-action="back-to-games">Back to games</button></div></div></section>`;
    const item = game.questions[game.index];
    if (!item) { game.stage = 'puzzle-result'; return renderPuzzleGame(); }
    return `<section class="stage-panel"><div class="stage-topline"><span class="pill purple">PUZZLE ${String(game.index + 1).padStart(2,'0')} / ${game.questions.length}</span><span class="pill">SCORE ${game.score * 10}</span><span class="pill mint">🔥 STREAK ${game.streak || 0}</span></div><div class="stage-progress"><span style="width:${game.index / game.questions.length * 100}%"></span></div><div class="stage-question"><span class="big-emoji">🧩</span><h2>${escapeHtml(item.q)}</h2><div style="padding:23px 12px;margin:16px auto 8px;max-width:650px;border:1px solid var(--line);border-radius:15px;background:rgba(255,255,255,.02);font:700 clamp(21px,4vw,32px) var(--display);letter-spacing:.03em">${escapeHtml(item.display)}</div></div>${game.answered ? `<div class="scenario-result" style="max-width:560px;margin:20px auto 0"><strong style="color:${game.lastCorrect ? 'var(--green)' : 'var(--red)'};font-size:12px">${game.lastCorrect ? 'Correct answer ✓' : `Not quite · Answer: ${escapeHtml(item.answer)}`}</strong><p style="font-size:11px;margin:7px 0 0">${escapeHtml(item.explain)}</p><div class="stage-actions"><button class="btn btn-primary" data-action="puzzle-next">${game.index === game.questions.length - 1 ? 'See results' : 'Next puzzle'} <i data-lucide="arrow-right"></i></button></div></div>` : `<div class="puzzle-options">${item.options.map(option => `<button class="puzzle-option" data-action="puzzle-answer" data-answer="${escapeHtml(option)}">${escapeHtml(option)}</button>`).join('')}</div><p class="small muted" style="text-align:center;margin-top:17px">Think it through. The explanation appears after you answer.</p>`}</section>`;
  }

  /* Create/join groups, posts and profiles */
  function makeInviteCode() {
    const chars = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
    let code = '';
    do { code = Array.from({ length: 6 }, () => chars[random(chars.length)]).join(''); } while (db.gcs.some(gc => gc.inviteCode === code));
    return code;
  }
  function openCreateGcModal() {
    showModal(`<span class="eyebrow">MAKE IT YOURS</span><h2 id="modalTitle" class="modal-content-title">Create a GC.</h2><p class="modal-subtitle">Give your group a name. Friends can join once with the invite code and it will stay in their My GCs.</p><form id="createGcForm" class="modal-form"><label>GC name<input class="field" name="name" placeholder="e.g. LPU Homies" maxlength="32" required></label><label>Pick a group vibe<div class="choice-pills">${['🔥','😂','🎮','💀','👑','🌙','🪩','🫂'].map((emoji,index) => `<button type="button" class="choice-pill ${index === 0 ? 'active' : ''}" data-action="choose-gc-emoji" data-emoji="${emoji}">${emoji}</button>`).join('')}</div><input type="hidden" name="emoji" value="🔥"></label><p class="form-help">Friends join from any device using the invite code. Only real signed-in users are added as members.</p><div class="modal-actions"><button type="button" class="btn btn-quiet" data-action="close-modal">Cancel</button><button class="btn btn-primary" type="submit">Create group <i data-lucide="arrow-up-right"></i></button></div></form>`);
  }
  function openJoinGcModal() {
    showModal(`<span class="eyebrow">FIND YOUR PEOPLE</span><h2 id="modalTitle" class="modal-content-title">Join a GC.</h2><p class="modal-subtitle">Enter the six-character invite code shared by the GC owner.</p><form id="joinGcForm" class="modal-form"><label>Invite code<input class="field join-code-input" name="code" maxlength="6" placeholder="ABC123" autocomplete="off" required></label><p class="form-help">Once you join, this group stays in your account's My GCs list. You will not need to add it again.</p><div class="modal-actions"><button type="button" class="btn btn-quiet" data-action="close-modal">Cancel</button><button class="btn btn-primary" type="submit">Join group <i data-lucide="arrow-up-right"></i></button></div></form>`);
  }
  function openConfessionModal() {
    const gcs = myGcs();
    if (confessionScope === 'gcs' && !gcs.length) {
      showModal(`<span class="eyebrow">ONE LAST THING</span><h2 id="modalTitle" class="modal-content-title">Choose your circle.</h2><p class="modal-subtitle">Create or join a GC before posting a group-only confession. You can also post to the global feed right now.</p><div class="stage-actions"><button class="btn btn-secondary" data-action="close-modal">Not now</button><button class="btn btn-primary" data-action="confession-scope" data-scope="global">Go global</button><button class="btn btn-quiet" data-action="create-gc">Create GC</button></div>`);
      return;
    }
    const defaultScope = confessionScope === 'global' ? 'global' : 'gc';
    showModal(`<span class="eyebrow">SAY IT, THEN LET IT GO</span><h2 id="modalTitle" class="modal-content-title">New confession.</h2><p class="modal-subtitle">Posts disappear after 24 hours. Anonymous hides your name from other readers, not from moderation.</p><form id="confessionForm" class="modal-form"><label>Where should it appear?<select class="select-field" name="scope" id="confessionScopeSelect"><option value="gc" ${defaultScope === 'gc' ? 'selected' : ''}>👥 One of my GCs</option><option value="global" ${defaultScope === 'global' ? 'selected' : ''}>🌐 Global GCVERSE feed</option></select></label><label id="confessionGcLabel">Choose GC<select class="select-field" name="gcId">${gcs.map(gc => `<option value="${gc.id}" ${gc.id === selectedGcId ? 'selected' : ''}>${escapeHtml(gc.emoji || '🔥')} ${escapeHtml(gc.name)}</option>`).join('')}</select></label><label>Confession<textarea class="textarea-field" name="content" minlength="3" maxlength="700" placeholder="What's on your mind? Keep it respectful—no doxxing or targeted harassment." required></textarea></label><label>Display identity<div class="choice-pills"><button type="button" class="choice-pill active" data-action="confession-identity" data-anonymous="true">🤫 Anonymous</button><button type="button" class="choice-pill" data-action="confession-identity" data-anonymous="false">👤 Show my name</button></div><input type="hidden" name="anonymous" value="true"></label><p class="form-help">Do not post another person's private information. Posts can be reported and are retained in the feed for 24 hours.</p><div class="modal-actions"><button type="button" class="btn btn-quiet" data-action="close-modal">Cancel</button><button class="btn btn-primary" type="submit">Post confession <i data-lucide="send"></i></button></div></form>`);
    const scopeSelect = $('#confessionScopeSelect');
    scopeSelect?.addEventListener('change', () => { const label = $('#confessionGcLabel'); if (label) label.style.display = scopeSelect.value === 'global' ? 'none' : 'grid'; });
    if (scopeSelect?.value === 'global' && $('#confessionGcLabel')) $('#confessionGcLabel').style.display = 'none';
  }
  function createGC(data) {
    const user = currentUser();
    const gc = { id: uid('gc'), name: data.name.trim(), emoji: data.emoji || '🔥', ownerId: currentUserId, inviteCode: makeInviteCode(), createdAt: now(), lastPlayedAt: 0, gamesPlayed: 0, members: [] };
    gc.members.push({ userId: currentUserId, name: user.name, role: 'owner', joinedAt: now(), xp: 0, gamesPlayed: 0, wins: 0, preview: false });
    if (data.previewMembers && !firebaseAuth.currentUser) {
      ['Alex','Maya','Arjun'].forEach((name, index) => gc.members.push({ userId: uid('preview'), name, role: 'member', joinedAt: now(), xp: [120,80,50][index], gamesPlayed: index, wins: index === 0 ? 1 : 0, preview: true, online: false }));
    }
    db.gcs.push(gc);
    selectedGcId = gc.id;
    prefsFor().lastGcId = gc.id;
    persist();
    closeModal();
    toast('GC created. Share the invite code with your friends.');
    setPage('games');
  }
  async function joinGC(code) {
    const normalized = code.trim().toUpperCase();
    try {
      const inviteSnap = await getDoc(doc(cloudStore, 'gcInvites', normalized));
      if (!inviteSnap.exists()) { toast('No GC found for that invite code, or its invite link is no longer valid.', 'error'); return; }
      const groupSnap = await getDoc(doc(cloudStore, 'gcs', inviteSnap.data().gcId));
      if (!groupSnap.exists()) { toast('That GC no longer exists.', 'error'); return; }
      const gc = readCloudDoc(groupSnap);
      if (memberFor(gc)) { selectedGcId = gc.id; closeModal(); setPage('games'); toast('You are already in this GC.'); return; }
      if ((gc.members || []).filter(member => !member.preview).length >= 50) return toast('This GC has reached its member limit.', 'error');
      gc.members ||= [];
      gc.members.push({ userId: currentUserId, name: currentUser().name, role: 'member', joinedAt: now(), xp: 0, gamesPlayed: 0, wins: 0, preview: false });
      gc.memberIds = [...new Set([...(gc.memberIds || []), currentUserId])];
      const index = db.gcs.findIndex(item => item.id === gc.id);
      if (index >= 0) db.gcs[index] = gc; else db.gcs.push(gc);
      selectedGcId = gc.id;
      prefsFor().lastGcId = gc.id;
      persist(); closeModal(); toast(`Joined ${gc.name}.`); setPage('games');
    } catch (error) { announceCloudError(error, 'Join GC'); }
  }
  function createConfession(data) {
    const item = { id: uid('confession'), authorId: currentUserId, authorName: currentUser().name, scope: data.scope, gcId: data.scope === 'gc' ? data.gcId : null, content: data.content.trim(), anonymous: data.anonymous, createdAt: now(), expiresAt: now() + 24 * 60 * 60 * 1000, likes: [], reports: 0 };
    db.confessions.push(item);
    if (item.anonymous) privateConfessionOwnerIds.add(item.id);
    persist();
    confessionScope = data.scope === 'global' ? 'global' : 'gcs';
    confessionGcFilter = data.gcId || 'all';
    closeModal();
    setPage('confessions');
    toast('Confession posted. It expires in 24 hours.');
  }

  /* Event handling */
  document.addEventListener('click', event => {
    const nav = event.target.closest('[data-nav]');
    if (nav) { event.preventDefault(); if (nav.dataset.nav === 'games') selectedGcId = ''; setPage(nav.dataset.nav); return; }
    const actionEl = event.target.closest('[data-action]');
    if (!actionEl) return;
    const action = actionEl.dataset.action;
    const id = actionEl.dataset.id;
    switch (action) {
      case 'close-modal': closeModal(); break;
      case 'start-couple-game': createCoupleRoom(actionEl.dataset.game); break;
      case 'join-couple-room': openJoinCoupleRoomModal(); break;
      case 'resume-couple-room': activeCoupleRoomId = id; setPage('couples'); break;
      case 'couple-back': activeCoupleRoomId = ''; setPage('couples'); break;
      case 'couple-answer-choice': saveCoupleAnswer(actionEl.dataset.answer || ''); break;
      case 'couple-next': { const room = coupleRoom(); if (!room || !coupleBothAnswered(room)) return toast('Both partners must answer first.', 'error'); const total = (coupleQuestions[room.gameId] || coupleQuestions.quiz).length; if (room.index + 1 >= total) { room.completedAt = now(); activeCoupleRoomId = ''; persist(); toast('Couples game completed. Nice work, both of you!'); setPage('couples'); } else { room.index += 1; persist(); renderPage(); } break; }
      case 'copy-couple-code': { const room = coupleRoom(id); if (!room) return; copyText(room.code).then(() => toast('Room code copied.')).catch(() => toast(`Room code: ${room.code}`)); break; }
      case 'chat-select-gc': chatTargetType = 'gc'; chatTargetId = id; renderPage(); break;
      case 'chat-select-dm': chatTargetType = 'dm'; chatTargetId = id; renderPage(); break;
      case 'clear-chat': { if (!confirm('Hide this conversation from your account? The other participants will still have their copies until expiry.')) return; const gc = chatTargetType === 'gc' ? getGc(chatTargetId) : null; const partner = chatTargetType === 'dm' ? chatTargetId : ''; const matching = db.messages.filter(message => gc ? (message.type === 'gc' && message.gcId === gc.id) : (message.type === 'dm' && [message.fromId, message.toId].includes(currentUserId) && [message.fromId, message.toId].includes(partner))); const prefs = prefsFor(); prefs.hiddenMessages = [...new Set([...(prefs.hiddenMessages || []), ...matching.map(message => message.id)])]; persist(); renderPage(); toast('Conversation hidden for your account.'); break; }
      case 'create-gc': closeModal(); openCreateGcModal(); break;
      case 'join-gc': closeModal(); openJoinGcModal(); break;
      case 'open-gc': selectedGcId = id; prefsFor().lastGcId = id; persist(); setPage('gc'); break;
      case 'select-gc': selectedGcId = id || selectedGcId; prefsFor().lastGcId = selectedGcId; persist(); setPage('games'); break;
      case 'switch-gc': selectedGcId = ''; setPage('games'); break;
      case 'copy-code': {
        const gc = getGc(selectedGcId);
        if (!gc) return toast('Choose a GC first.', 'error');
        copyText(gc.inviteCode).then(() => toast(`Invite code ${gc.inviteCode} copied.`)).catch(() => toast(`Invite code: ${gc.inviteCode}`));
        break;
      }
      case 'start-game': startGame(actionEl.dataset.game); break;
      case 'quick-game': {
        const targetGame = actionEl.dataset.game;
        if (getGc(selectedGcId)) startGame(targetGame);
        else if (myGcs().length === 1) { selectedGcId = myGcs()[0].id; startGame(targetGame); }
        else { setPage('games'); toast('Choose a GC before starting this game.'); }
        break;
      }
      case 'dismiss-creator': prefsFor().creatorDismissed = true; persist(); renderPage(); toast('Creator recommendations hidden.'); break;
      case 'show-creator': prefsFor().creatorDismissed = false; persist(); renderPage(); break;
      case 'open-project': {
        event.preventDefault();
        const project = actionEl.dataset.project;
        const url = PROJECT_LINKS[project];
        if (url && /^https?:\/\//i.test(url)) window.open(url, '_blank', 'noopener,noreferrer');
        else toast(`Add the real ${project === 'studyflow' ? 'StudyFlow' : 'SpendNest'} URL in script.js first.`, 'error');
        break;
      }
      case 'show-about': showModal(`<span class="eyebrow">ABOUT THIS BUILD</span><h2 id="modalTitle" class="modal-content-title">GCVERSE, connected.</h2><p class="modal-subtitle">GCVERSE is connected to Firebase Authentication and Cloud Firestore. Profiles, GCs, confessions, messages, couple rooms and game history are stored in the cloud, subject to the published Firestore Security Rules.</p><div class="setting-row"><div><strong>Confessions</strong><p>Expired after 24 hours; Firestore TTL removes records after its cleanup delay.</p></div><span class="pill">24H</span></div><div class="setting-row"><div><strong>Game sessions</strong><p>Detailed sessions expire after seven days; aggregate XP remains.</p></div><span class="pill">7D</span></div><div class="modal-actions" style="margin-top:18px"><button class="btn btn-primary" data-action="close-modal">Got it</button></div>`); break;
      case 'create-confession': closeModal(); openConfessionModal(); break;
      case 'confession-scope': confessionScope = actionEl.dataset.scope; confessionGcFilter = 'all'; if ($('#modalOverlay').classList.contains('open')) { closeModal(); } setPage('confessions'); break;
      case 'confession-identity': {
        const form = $('#confessionForm'); if (!form) return;
        const anonymous = actionEl.dataset.anonymous === 'true';
        form.elements.anonymous.value = String(anonymous);
        $$('[data-action="confession-identity"]', form).forEach(btn => btn.classList.toggle('active', btn === actionEl));
        break;
      }
      case 'like-confession': {
        const post = db.confessions.find(item => item.id === id); if (!post) return;
        post.likes ||= [];
        post.likes = post.likes.includes(currentUserId) ? post.likes.filter(uidValue => uidValue !== currentUserId) : [...post.likes, currentUserId];
        persist(); renderPage(); break;
      }
      case 'report-confession': {
        const post = db.confessions.find(item => item.id === id); if (!post) return;
        post.reports = (post.reports || 0) + 1; persist(); toast('Report recorded. A moderator review workflow still needs to be added.'); break;
      }
      case 'confession-menu': showModal(`<span class="eyebrow">POST OPTIONS</span><h2 id="modalTitle" class="modal-content-title">Manage this confession.</h2><p class="modal-subtitle">You can hide posts from your preview or report content that breaks the rules.</p><div class="stage-actions"><button class="btn btn-secondary" data-action="report-confession" data-id="${id}"><i data-lucide="flag"></i> Report</button><button class="btn btn-primary" data-action="hide-confession" data-id="${id}">Hide from my feed</button></div>`); break;
      case 'hide-confession': {
        const item = db.confessions.find(post => post.id === id); if (item) { item.hiddenFor ||= []; item.hiddenFor.push(currentUserId); persist(); }
        closeModal(); toast('Hidden from your feed.'); setPage('confessions'); break;
      }
      case 'dismiss-creator': prefsFor().creatorDismissed = true; persist(); renderPage(); break;
      case 'choose-gc-emoji': {
        const form = $('#createGcForm'); if (!form) return;
        form.elements.emoji.value = actionEl.dataset.emoji;
        $$('[data-action="choose-gc-emoji"]', form).forEach(btn => btn.classList.toggle('active', btn === actionEl));
        break;
      }
      case 'gc-leaderboard': setPage('leaderboard'); break;
      case 'toggle-sidebar': $('#sidebar').classList.toggle('mobile-open'); break;
      case 'sign-out': case 'logout': void signOut(firebaseAuth); break;
      case 'td-demo': {
        const gc = getGc(game.gcId);
        const me = memberFor(gc);
        game.players = [me?.userId || currentUserId, `${currentUserId}_sample_guest`];
        game.guestPlayers = [{ userId: `${currentUserId}_sample_guest`, name: 'Sample Guest', preview: true }];
        game.choices = {};
        game.stage = 'td-preferences'; renderPage(); break;
      }
      case 'td-preferences': {
        const selected = game.players || [];
        if (selected.length !== 2) return toast('Select exactly two players.', 'error');
        const gc = getGc(game.gcId);
        if (!game.guestPlayers) game.guestPlayers = [];
        selected.forEach(playerId => { if (!game.choices[playerId]) game.choices[playerId] = {}; });
        game.stage = 'td-preferences'; renderPage(); break;
      }
      case 'td-choice': {
        const player = actionEl.dataset.player;
        game.choices[player] ||= {};
        game.choices[player].preference = actionEl.dataset.pref;
        const custom = $(`[data-td-custom="${CSS.escape(player)}"]`);
        if (custom) game.choices[player].custom = custom.value;
        renderPage(); break;
      }
      case 'td-back': game.stage = 'td-setup'; renderPage(); break;
      case 'td-reveal': {
        $$('.textarea-field[data-td-custom]').forEach(textarea => { const playerId = textarea.dataset.tdCustom; game.choices[playerId] ||= {}; game.choices[playerId].custom = textarea.value.trim(); });
        const players = game.players.map(playerId => findPlayerForGame(playerId)).filter(Boolean);
        if (players.length !== 2 || players.some(player => !game.choices[player.userId]?.preference)) return toast('Both players must lock a preference.', 'error');
        game.assignments = players.map((player,index) => getTruthDareAssignment(player,index)); game.index = 0; game.stage = 'td-reveal'; renderPage(); break;
      }
      case 'td-next': {
        if (game.index === 0) { game.index = 1; renderPage(); }
        else if (game.round < 3) { game.round += 1; game.players = [...game.players]; game.choices = {}; game.assignments = []; game.stage = 'td-preferences'; renderPage(); }
        else finishGame(90, 'Both players completed three Truth & Dare rounds.', false);
        break;
      }
      case 'redflag-answer': {
        game.answers.push({ index: game.index, value: actionEl.dataset.value });
        game.index += 1;
        if (game.index >= game.questions.length) { game.stage = 'redflag-result'; }
        renderPage(); break;
      }
      case 'redflag-finish': finishGame(80, `You judged ${game.questions.length} relationship scenarios and built your red-flag profile.`, false); break;
      case 'challenge-done': {
        const assignment = (game.rounds[game.round - 1] || []).find(item => item.userId === currentUserId) || (game.rounds[game.round - 1] || [])[0];
        if (assignment) {
          assignment.done = true;
          const difficultyXp = assignment.challenge?.category === 'final' ? 50 : ({ easy: 10, medium: 20, hard: 30 }[assignment.challenge?.difficulty] || 10);
          game.xp += difficultyXp;
        }
        renderPage(); break;
      }
      case 'challenge-reroll': {
        if (game.rerollUsed) return;
        const assignments = game.rounds[game.round - 1] || [];
        const own = assignments.find(item => item.userId === currentUserId) || assignments[0];
        const available = challengePrompts.filter(item => !game.used.includes(item.id));
        if (!own || !available.length) return toast('No unused challenges left.', 'error');
        const next = pick(available); game.used.push(next.id); own.challenge = next; game.rerollUsed = true; renderPage(); toast('Challenge rerolled. The old one cannot be reused.'); break;
      }
      case 'challenge-next': {
        if (game.round < 4) { game.round += 1; game.rerollUsed = false; assignChallengeRound(); renderPage(); }
        else finishGame(game.xp + 40, 'Four rounds completed. Every player received a different challenge each round.', false);
        break;
      }
      case 'tmkoc-start': {
        if (!game.players.length) return toast('Choose at least one participant.', 'error');
        game.stage = 'tmkoc-quiz'; game.activePlayerIndex = 0; game.playerResults = []; game.index = 0; game.scores = { chaos:0, drama:0, confidence:0, loyalty:0, logic:0 }; game.answers = []; renderPage(); break;
      }
      case 'tmkoc-next-player': {
        game.activePlayerIndex += 1; game.index = 0; game.scores = { chaos:0, drama:0, confidence:0, loyalty:0, logic:0 }; game.answers = []; game.stage = 'tmkoc-quiz'; renderPage(); break;
      }
      case 'tmkoc-answer': {
        const option = game.questions[game.index].options[Number(actionEl.dataset.option)];
        if (option) game.scores[option.s] += 1;
        game.answers.push(option?.s || ''); game.index += 1;
        if (game.index >= game.questions.length) {
          const player = findPlayerForGame(game.players[game.activePlayerIndex]) || currentUser();
          game.playerResults.push({ userId: player.userId, name: player.name, scores: { ...game.scores } });
          if (game.activePlayerIndex < game.players.length - 1) game.stage = 'tmkoc-pass';
          else { game.assignments = assignUniqueTMKOCCharacters(game.playerResults); game.stage = 'tmkoc-group-result'; }
        }
        renderPage(); break;
      }
      case 'tmkoc-finish': {
        const own = game.assignments.find(item => item.userId === currentUserId) || game.assignments[0];
        finishGame(60, `Your GC cast was assigned unique characters. You matched with ${own?.character?.name || 'a TMKOC character'}.`, false); break;
      }
      case 'tmkoc-restart': startGame('tmkoc'); break;
      case 'xo-start': {
        game.mode = actionEl.dataset.mode; game.stage = 'xo-board'; game.board = Array(9).fill(''); game.turn = 'X'; game.finished = false; game.winner = null; game.winning = []; game.difficulty = 'hard'; renderPage(); break;
      }
      case 'xo-move': {
        if (game.finished || game.board[Number(actionEl.dataset.index)] || (game.mode === 'computer' && game.turn !== 'X')) return;
        const index = Number(actionEl.dataset.index); game.board[index] = game.turn; evaluateXO();
        if (!game.finished && game.mode === 'computer' && game.turn === 'O') { const move = chooseComputerMove(game.board, game.difficulty); if (move !== -1) { game.board[move] = 'O'; evaluateXO(); } }
        renderPage(); break;
      }
      case 'xo-reset': game.board = Array(9).fill(''); game.turn = 'X'; game.finished = false; game.winner = null; game.winning = []; renderPage(); break;
      case 'xo-finish': finishGame(game.winner === 'X' ? 50 : 15, game.winner === 'X' ? 'You won the XO match.' : game.winner === 'O' ? 'The match ended with an opponent win.' : 'A draw is still a good rematch setup.', game.winner === 'X'); break;
      case 'puzzle-answer': {
        if (game.answered) return;
        const question = game.questions[game.index]; const answer = actionEl.dataset.answer;
        game.answered = true; game.lastCorrect = answer === question.answer;
        if (game.lastCorrect) { game.score += 1; game.streak = (game.streak || 0) + 1; game.bestStreak = Math.max(game.bestStreak || 0, game.streak); }
        else game.streak = 0;
        renderPage(); break;
      }
      case 'puzzle-next': {
        game.index += 1; game.answered = false;
        if (game.index >= game.questions.length) {
          finishGame(game.score * 10, `You solved ${game.score} out of ${game.questions.length} puzzles.`, game.score >= 9);
          game.stage = 'puzzle-result';
          renderPage();
        } else renderPage();
        break;
      }
      case 'replay-game': startGame(game?.id || actionEl.dataset.game || 'puzzle'); break;
      case 'back-to-games': game = null; page = 'games'; renderSidebar(); renderPage(); window.scrollTo({top:0,behavior:'smooth'}); break;
      case 'share-result': {
        const text = `GCVERSE · ${gameInfo[game?.id]?.title || 'Game'}\n${game?.result?.summary || 'Finished a game'}\n+${game?.result?.xp || 0} XP`;
        copyText(text).then(() => toast('Result copied. Share it with your GC.')).catch(() => toast(text)); break;
      }
      default: break;
    }
  });

  function findPlayerForGame(playerId) {
    const gc = getGc(game.gcId);
    return gc?.members.find(member => member.userId === playerId) || game.guestPlayers?.find(member => member.userId === playerId) || (playerId === currentUserId ? { userId: currentUserId, name: currentUser()?.name || 'You' } : null);
  }
  function copyText(value) {
    if (navigator.clipboard?.writeText) return navigator.clipboard.writeText(value);
    return new Promise((resolve, reject) => {
      const textarea = document.createElement('textarea'); textarea.value = value; textarea.style.position = 'fixed'; textarea.style.opacity = '0'; document.body.appendChild(textarea); textarea.select();
      try { document.execCommand('copy') ? resolve() : reject(); } catch (error) { reject(error); } finally { textarea.remove(); }
    });
  }
  function evaluateXO() {
    const combos = [[0,1,2],[3,4,5],[6,7,8],[0,3,6],[1,4,7],[2,5,8],[0,4,8],[2,4,6]];
    const line = combos.find(combo => game.board[combo[0]] && game.board[combo[0]] === game.board[combo[1]] && game.board[combo[1]] === game.board[combo[2]]);
    if (line) { game.finished = true; game.winner = game.board[line[0]]; game.winning = line; }
    else if (game.board.every(Boolean)) { game.finished = true; game.winner = 'draw'; }
    else game.turn = game.turn === 'X' ? 'O' : 'X';
  }
  function chooseComputerMove(board, difficulty = 'hard') {
    const empty = board.map((value,index) => value ? -1 : index).filter(index => index >= 0);
    if (!empty.length) return -1;
    if (difficulty === 'easy' || (difficulty === 'medium' && Math.random() < .42)) return pick(empty);
    let bestScore = -Infinity, bestMove = empty[0];
    for (const move of empty) {
      board[move] = 'O';
      const score = minimax(board, 0, false);
      board[move] = '';
      if (score > bestScore) { bestScore = score; bestMove = move; }
    }
    return bestMove;
  }
  function minimax(board, depth, isMaximizing) {
    const result = getBoardWinner(board);
    if (result === 'O') return 10 - depth;
    if (result === 'X') return depth - 10;
    if (result === 'draw') return 0;
    const empty = board.map((value,index) => value ? -1 : index).filter(index => index >= 0);
    if (isMaximizing) {
      let best = -Infinity; for (const move of empty) { board[move] = 'O'; best = Math.max(best,minimax(board,depth+1,false)); board[move] = ''; } return best;
    }
    let best = Infinity; for (const move of empty) { board[move] = 'X'; best = Math.min(best,minimax(board,depth+1,true)); board[move] = ''; } return best;
  }
  function getBoardWinner(board) {
    const combos = [[0,1,2],[3,4,5],[6,7,8],[0,3,6],[1,4,7],[2,5,8],[0,4,8],[2,4,6]];
    const line = combos.find(combo => board[combo[0]] && board[combo[0]] === board[combo[1]] && board[combo[1]] === board[combo[2]]);
    if (line) return board[line[0]];
    if (board.every(Boolean)) return 'draw';
    return null;
  }

  document.addEventListener('input', event => {
    if (event.target.id === 'chatUserSearch') {
      const term = String(event.target.value || '').toLowerCase().trim();
      $$('.chat-user-row').forEach(row => { row.style.display = (row.dataset.userSearch || '').includes(term) ? 'flex' : 'none'; });
    }
  });

  document.addEventListener('change', event => {
    if (event.target.matches('[data-player-select]')) {
      const id = event.target.dataset.playerSelect;
      if (event.target.checked) {
        if (game.players.length < 2) game.players.push(id); else event.target.checked = false;
      } else game.players = game.players.filter(value => value !== id);
      renderPage();
    }
    if (event.target.matches('[data-tmkoc-select]')) {
      const id = event.target.dataset.tmkocSelect;
      if (event.target.checked) { if (game.players.length < 10) game.players.push(id); else event.target.checked = false; }
      else { game.players = game.players.filter(value => value !== id); if (!game.players.length) game.players = [currentUserId]; }
      renderPage();
    }
    if (event.target.id === 'confessionGcFilter') { confessionGcFilter = event.target.value; renderPage(); }
    if (event.target.id === 'creatorToggle') { prefsFor().creatorDismissed = !event.target.checked; persist(); toast(event.target.checked ? 'Creator picks will be shown.' : 'Creator picks hidden.'); }
  });

  document.addEventListener('submit', async event => {
    const form = event.target;
    event.preventDefault();
    if (form.id === 'chatMessageForm') {
      const data = new FormData(form);
      const text = String(data.get('message') || '').trim();
      if (!text) return;
      const type = String(data.get('type') || 'gc');
      const gcId = String(data.get('gcId') || '');
      const recipientId = String(data.get('recipientId') || '');
      if (type === 'gc' && !memberFor(getGc(gcId))) return toast('You must belong to this GC to message here.', 'error');
      if (type === 'dm' && (!db.users[recipientId] || recipientId === currentUserId)) return toast('Choose a valid direct-message recipient.', 'error');
      db.messages.push({ id: uid('msg'), type, gcId: type === 'gc' ? gcId : null, fromId: currentUserId, toId: type === 'dm' ? recipientId : null, text, createdAt: now(), expiresAt: now() + 10 * 60 * 1000 });
      persist(); renderPage();
      const box = $('#chatMessages'); if (box) box.scrollTop = box.scrollHeight;
      return;
    }
    if (form.id === 'coupleAnswerForm') {
      const answer = String(new FormData(form).get('answer') || '').trim();
      if (!answer) return toast('Write your answer before locking it in.', 'error');
      saveCoupleAnswer(answer);
      return;
    }
    if (form.id === 'joinCoupleRoomForm') {
      const code = String(new FormData(form).get('code') || '').trim().toUpperCase();
      try {
        const codeSnap = await getDoc(doc(cloudStore, 'coupleRoomCodes', code));
        if (!codeSnap.exists()) return toast('No active room with that code was found.', 'error');
        const roomSnap = await getDoc(doc(cloudStore, 'coupleRooms', codeSnap.data().roomId));
        if (!roomSnap.exists()) return toast('This room has expired or no longer exists.', 'error');
        const room = readCloudDoc(roomSnap);
        if (room.expiresAt && room.expiresAt <= now()) return toast('This room has expired.', 'error');
        if (room.ownerId === currentUserId || room.partnerId === currentUserId) { activeCoupleRoomId = room.id; closeModal(); setPage('couples'); return; }
        if (room.partnerId && room.partnerId !== currentUserId) return toast('This room already has two players.', 'error');
        room.partnerId = currentUserId;
        room.memberIds = [room.ownerId, currentUserId];
        room.responses ||= {}; room.answeredBy ||= {};
        const localIndex = db.coupleRooms.findIndex(item => item.id === room.id);
        if (localIndex >= 0) db.coupleRooms[localIndex] = room; else db.coupleRooms.push(room);
        activeCoupleRoomId = room.id;
        persist(); closeModal(); setPage('couples'); toast('Joined the private couples room.');
      } catch (error) { announceCloudError(error, 'Join couple room'); }
      return;
    }
    if (form.id === 'authForm') {
      const data = new FormData(form);
      const name = String(data.get('name') || '').trim();
      const email = String(data.get('email') || '').trim().toLowerCase();
      const password = String(data.get('password') || '');
      if (name.length < 2 || !email || password.length < 6) return toast('Enter a display name, valid email and password with at least 6 characters.', 'error');
      pendingDisplayName = name;
      try {
        let credential;
        try {
          credential = await createUserWithEmailAndPassword(firebaseAuth, email, password);
          await updateProfile(credential.user, { displayName: name });
        } catch (createError) {
          if (createError?.code !== 'auth/email-already-in-use') throw createError;
          pendingDisplayName = '';
          credential = await signInWithEmailAndPassword(firebaseAuth, email, password);
        }
        // onAuthStateChanged bootstraps the profile and loads the cloud collections.
      } catch (error) {
        pendingDisplayName = '';
        toast(loginErrorMessage(error), 'error');
      }
    }
    if (form.id === 'createGcForm') {
      const data = new FormData(form);
      const name = String(data.get('name') || '').trim();
      if (name.length < 2) return toast('Choose a GC name with at least two characters.', 'error');
      createGC({ name, emoji: String(data.get('emoji') || '🔥'), previewMembers: data.get('previewMembers') === 'on' });
    }
    if (form.id === 'joinGcForm') joinGC(String(new FormData(form).get('code') || ''));
    if (form.id === 'confessionForm') {
      const data = new FormData(form); const scope = String(data.get('scope'));
      const content = String(data.get('content') || '').trim();
      if (content.length < 3) return toast('Add a little more to your confession.', 'error');
      const gcId = String(data.get('gcId') || '');
      if (scope === 'gc' && !memberFor(getGc(gcId))) return toast('Choose a GC you belong to.', 'error');
      createConfession({ scope, content, gcId, anonymous: String(data.get('anonymous')) === 'true' });
    }
    if (form.id === 'profileForm') {
      const profileData = new FormData(form);
      const name = String(profileData.get('displayName') || '').trim();
      const username = normalizeUsername(profileData.get('username') || '');
      if (name.length < 2) return toast('Display name must have at least two characters.', 'error');
      if (username.length < 3 || !/^[a-z0-9._]+$/.test(username)) return toast('Username must be 3–20 characters using letters, numbers, dots or underscores.', 'error');
      if (Object.values(db.users).some(user => user.id !== currentUserId && normalizeUsername(user.username) === username)) return toast('That username is already taken. Choose another one.', 'error');
      try {
        await updateCloudProfile(name, username);
        render(); toast('Profile updated and saved to Firestore.');
      } catch (error) { toast(error?.message || 'Could not update profile.', 'error'); }
    }
  });

  $('#googlePreviewButton').addEventListener('click', async () => {
    try {
      const provider = new GoogleAuthProvider();
      await signInWithPopup(firebaseAuth, provider);
    } catch (error) { toast(loginErrorMessage(error), 'error'); }
  });
  $('#modalClose').addEventListener('click', closeModal);
  $('#modalOverlay').addEventListener('click', event => { if (event.target === $('#modalOverlay')) closeModal(); });
  document.addEventListener('keydown', event => {
    if (event.key === 'Escape') { closeModal(); $('#sidebar').classList.remove('mobile-open'); }
  });
  $('#mobileMenuButton').addEventListener('click', () => $('#sidebar').classList.toggle('mobile-open'));
  $('#sidebarCollapse').addEventListener('click', () => $('#sidebar').classList.toggle('mobile-open'));
  $('#signOutButton').addEventListener('click', async () => { try { await signOut(firebaseAuth); } catch (error) { toast(loginErrorMessage(error), 'error'); } });
  $('#resetDemoButton').addEventListener('click', () => {
    localStorage.removeItem(DB_KEY);
    toast('Local cache cleared. Your Firebase account and cloud data were not deleted.');
  });

  // Authentication is the session source of truth; all app data loads after auth is ready.
  ensureExtendedNavigation();
  onAuthStateChanged(firebaseAuth, user => {
    authStateRun += 1;
    void handleFirebaseAuthChange(user, authStateRun);
  });
  setInterval(() => {
    if ((page === 'confessions' || page === 'chats' || page === 'couples') && currentUser()) renderPage();
    if (currentUser()) cleanExpired();
  }, 30000);
})();
