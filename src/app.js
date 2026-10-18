import { auth, db, googleProvider } from './firebase.js';
import {
  onAuthStateChanged, signInWithPopup, signInWithRedirect, getRedirectResult, signOut
} from 'https://www.gstatic.com/firebasejs/11.10.0/firebase-auth.js';
import {
  arrayUnion, collection, deleteDoc, doc, getDoc, getDocs, limit, onSnapshot, query,
  runTransaction, setDoc, updateDoc, where, writeBatch
} from 'https://www.gstatic.com/firebasejs/11.10.0/firebase-firestore.js';
import {
  gameInfo, coupleGameInfo, truthPrompts, darePrompts, redFlagScenarios,
  challengePrompts, tmkocCharacters, tmkocQuestions, puzzleQuestions, coupleQuestions
} from './game-content.js';

const $ = (selector, root = document) => root.querySelector(selector);
const $$ = (selector, root = document) => [...root.querySelectorAll(selector)];
const pageNames = {
  dashboard: 'Dashboard', chats: 'Chats', groups: 'Groups / GCs', games: 'Gaming Hub',
  confessions: 'Confessions', couples: 'Couples Corner', ranks: 'Ranks', profile: 'Profile & settings', game: 'Game'
};
const sectionMeta = {
  chats: { icon: '☏', title: 'Chats', description: 'Find a homie, send a request, and chat after they accept.' },
  groups: { icon: '♧', title: 'Groups / GCs', description: 'Create a GC, join with a code and talk with your crew.' },
  confessions: { icon: '♡', title: 'Confessions', description: 'Share a thought, react to posts and report content that should be reviewed.' },
  couples: { icon: '♥', title: 'Couples Corner', description: 'Create a private room, invite your partner and answer together.' },
  ranks: { icon: '♜', title: 'Ranks', description: 'XP, games played and wins are loaded from Firestore.' }
};
const gameCategory = {
  truth: 'Group game', redflag: 'Group game', challenge: 'Group game', tmkoc: 'Group game', xo: 'Puzzle / 2-player', puzzle: 'Solo puzzle'
};
const CONFESSION_LIFETIME_MS = 24 * 60 * 60 * 1000;
const MESSAGE_LIFETIME_MS = 30 * 24 * 60 * 60 * 1000;

let currentProfile = null;
let currentStats = { xp: 0, gamesPlayed: 0, wins: 0, streak: 0, bestPuzzle: 0 };
let currentRank = null;
let activePage = 'dashboard';
let activeGameId = '';
let toastTimer = 0;
let authBusy = false;
let pageUnsubs = [];
let chatSearchResult = null;
let chatViewMode = 'inbox';
let activeChatTab = 'messages';
let coupleRoundAnswers = {};
const profileCache = new Map();
const state = {
  connections: [], incomingRequests: [], outgoingRequests: [], dmMessages: [],
  selectedConnectionId: '',
  groups: [], groupMessages: [], selectedGroupId: '',
  confessions: [], groupConfessions: [], selectedConfessionGroupId: 'global',
  rooms: [], selectedRoomId: '',
  rankEntries: [], rankLoading: false,
  prefs: { showOnline: true, showLastSeen: true },
  errors: {}
};
let gameRun = null;
let selectedCoupleGameId = 'quiz';

function escapeHTML(value = '') {
  return String(value).replace(/[&<>"']/g, char => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[char]));
}
function initials(name = '') {
  return String(name).trim().split(/\s+/).slice(0, 2).map(part => part[0] || '').join('').toUpperCase() || '?';
}
function normalizeUsername(value = '') {
  return String(value).trim().replace(/^@+/, '').toLowerCase();
}
function isValidUsername(value) {
  return value.length >= 3 && value.length <= 20 && /^[a-z0-9](?:[a-z0-9._]{1,18}[a-z0-9])$/.test(value) && !/[._]{2}/.test(value);
}
function showToast(message, type = '') {
  const toast = $('#toast');
  if (!toast) return;
  toast.textContent = message;
  toast.className = `toast show ${type}`.trim();
  window.clearTimeout(toastTimer);
  toastTimer = window.setTimeout(() => { toast.className = 'toast'; }, 3200);
}
function setStatus(element, message = '', type = '') {
  if (!element) return;
  element.textContent = message;
  element.className = `status-message ${type}`.trim();
}
function setAuthView(view) {
  $('#authView').classList.toggle('hidden', view !== 'auth');
  $('#profileView').classList.toggle('hidden', view !== 'profile');
  $('#appShell').classList.toggle('hidden', view !== 'app');
}
function setLoading(button, loading, label = 'Continue with Google') {
  if (!button) return;
  button.disabled = loading;
  const text = button.querySelector('span:nth-child(2)');
  if (text) text.textContent = loading ? 'Connecting securely…' : label;
}
function now() { return Date.now(); }
function uid() { return auth.currentUser?.uid || ''; }
function sortedPairId(first, second) { return [first, second].sort().join('__'); }
function formatNumber(value) {
  const number = Number(value);
  return Number.isFinite(number) && number >= 0 ? Math.floor(number).toLocaleString() : '0';
}
function safeDate(value) {
  const n = Number(value);
  if (!Number.isFinite(n) || n <= 0) return '';
  return new Date(n).toLocaleString([], { month: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit' });
}
function randomCode(length = 6) {
  const alphabet = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  let result = '';
  for (let i = 0; i < length; i++) result += alphabet[Math.floor(Math.random() * alphabet.length)];
  return result;
}
function shuffle(items) {
  const copy = [...items];
  for (let i = copy.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [copy[i], copy[j]] = [copy[j], copy[i]];
  }
  return copy;
}
function activeUserSummary() {
  return { id: uid(), name: currentProfile?.name || 'Homie', username: currentProfile?.username || '', joinedAt: now() };
}
function draftValues() {
  const result = {};
  $$('#pageView [name]').forEach(element => {
    const key = `${element.tagName}:${element.name}`;
    result[key] = element.type === 'checkbox' ? element.checked : element.value;
  });
  return result;
}
function restoreDraftValues(values) {
  $$('#pageView [name]').forEach(element => {
    const key = `${element.tagName}:${element.name}`;
    if (!(key in values)) return;
    if (element.type === 'checkbox') element.checked = values[key];
    else element.value = values[key];
  });
}
function clearPageListeners() {
  pageUnsubs.forEach(unsub => { try { unsub(); } catch { /* listener already closed */ } });
  pageUnsubs = [];
}
function reRenderPage() { renderPage(false); }
function profileFor(userId) {
  if (userId === uid()) return currentProfile || { id: userId, name: 'You', username: '' };
  return profileCache.get(userId) || { id: userId, name: `Homie ${String(userId).slice(-4)}`, username: '' };
}
async function cacheProfile(userId) {
  if (!userId || profileCache.has(userId) || userId === uid()) return;
  try {
    const snap = await getDoc(doc(db, 'users', userId));
    if (snap.exists()) profileCache.set(userId, { ...snap.data(), id: userId });
  } catch (error) {
    console.warn('[GCVERSE] Could not read profile:', error?.code || error?.message || error);
  }
}
async function cacheProfiles(userIds) {
  const unique = [...new Set(userIds.filter(id => id && id !== uid() && !profileCache.has(id)))].slice(0, 40);
  await Promise.all(unique.map(cacheProfile));
}
function errorText(error, fallback = 'Something went wrong. Please try again.') {
  const code = error?.code || '';
  if (code === 'permission-denied') return 'Firebase blocked this action. Check the deployed Firestore Rules for this feature.';
  if (code === 'unavailable' || code === 'network-request-failed') return 'Network issue. Check your connection and try again.';
  if (code === 'failed-precondition') return 'Firestore needs an index for this query, or the current database state does not allow this action.';
  if (code === 'already-exists') return 'That item already exists.';
  return fallback;
}
function listen(q, onData, label) {
  const unsub = onSnapshot(q, snapshot => onData(snapshot), error => {
    console.error(`[GCVERSE] ${label} listener failed:`, error);
    state.errors[label] = errorText(error, `Could not load ${label}.`);
    reRenderPage();
  });
  pageUnsubs.push(unsub);
}

// Authentication and first-time profile setup
async function beginGoogleSignIn() {
  if (authBusy) return;
  authBusy = true;
  const button = $('#googleSignIn');
  setLoading(button, true);
  setStatus($('#authStatus'), 'Opening Google sign-in…');
  try {
    await signInWithPopup(auth, googleProvider);
    setStatus($('#authStatus'), 'Signed in. Loading your space…', 'success');
  } catch (error) {
    if (error?.code === 'auth/popup-blocked' || error?.code === 'auth/operation-not-supported-in-this-environment') {
      try { await signInWithRedirect(auth, googleProvider); return; }
      catch (redirectError) { setStatus($('#authStatus'), friendlyAuthError(redirectError), 'error'); }
    } else setStatus($('#authStatus'), friendlyAuthError(error), 'error');
  } finally {
    authBusy = false;
    setLoading(button, false);
  }
}
function friendlyAuthError(error) {
  switch (error?.code) {
    case 'auth/popup-closed-by-user': return 'Google sign-in was closed before it finished. Try again when ready.';
    case 'auth/unauthorized-domain': return 'This site domain is not authorized in Firebase Authentication settings yet.';
    case 'auth/network-request-failed': return 'Network issue. Check your connection and try again.';
    case 'auth/cancelled-popup-request': return 'A sign-in window is already open. Finish it or try again.';
    case 'auth/too-many-requests': return 'Too many attempts. Wait a little and try again.';
    default: return 'Could not sign in right now. Please try again.';
  }
}
async function readOrInitializeProfile(user) {
  const profileSnap = await getDoc(doc(db, 'users', user.uid));
  if (!profileSnap.exists()) return null;
  const data = profileSnap.data();
  if (!data.name || !isValidUsername(normalizeUsername(data.username || ''))) return null;
  return { ...data, id: user.uid };
}
function suggestUsername(name) {
  let base = normalizeUsername(name.replace(/\s+/g, '.').replace(/[^a-zA-Z0-9._]/g, ''))
    .replace(/[._]{2,}/g, '.').replace(/^[._]+|[._]+$/g, '').slice(0, 20);
  if (base.length < 3) base = `${base || 'player'}${base.length === 0 ? '123' : '01'}`.slice(0, 20);
  return base;
}
async function showProfileSetup(user, existing = null) {
  setAuthView('profile');
  $('#displayName').value = String(existing?.name || user.displayName || '').slice(0, 24);
  $('#username').value = normalizeUsername(existing?.username || suggestUsername(user.displayName || user.email?.split('@')[0] || 'player'));
  setStatus($('#profileStatus'), 'Your username must be unique across GCVERSE.');
}
async function saveProfile(event) {
  event.preventDefault();
  const user = auth.currentUser;
  if (!user) return;
  const name = $('#displayName').value.trim().replace(/\s+/g, ' ');
  const username = normalizeUsername($('#username').value);
  if (name.length < 2 || name.length > 24) return setStatus($('#profileStatus'), 'Display name must be between 2 and 24 characters.', 'error');
  if (!isValidUsername(username)) return setStatus($('#profileStatus'), 'Use 3–20 lowercase letters, numbers, dots or underscores. Start and end with a letter or number.', 'error');
  const submit = $('#profileForm button[type="submit"]');
  submit.disabled = true;
  submit.querySelector('span:first-child').textContent = 'Saving your profile…';
  setStatus($('#profileStatus'), 'Checking username availability…');
  try {
    const userRef = doc(db, 'users', user.uid);
    const usernameRef = doc(db, 'usernames', username);
    const statsRef = doc(db, 'stats', user.uid);
    const prefsRef = doc(db, 'userPrefs', user.uid);
    const newCreatedAt = now();
    await runTransaction(db, async transaction => {
      const [userSnap, usernameSnap, statsSnap, prefsSnap] = await Promise.all([
        transaction.get(userRef), transaction.get(usernameRef), transaction.get(statsRef), transaction.get(prefsRef)
      ]);
      const oldProfile = userSnap.exists() ? userSnap.data() : {};
      const oldUsername = normalizeUsername(oldProfile.username || '');
      let oldUsernameSnap = null;
      let oldUsernameRef = null;
      if (oldUsername && oldUsername !== username) {
        oldUsernameRef = doc(db, 'usernames', oldUsername);
        oldUsernameSnap = await transaction.get(oldUsernameRef);
      }
      if (usernameSnap.exists() && usernameSnap.data().userId !== user.uid) throw new Error('USERNAME_TAKEN');
      const createdAt = Number(oldProfile.createdAt) || newCreatedAt;
      transaction.set(usernameRef, { id: username, userId: user.uid, createdAt });
      if (oldUsernameRef && oldUsernameSnap?.exists() && oldUsernameSnap.data().userId === user.uid) transaction.delete(oldUsernameRef);
      transaction.set(userRef, { id: user.uid, name, username, avatar: initials(name), createdAt });
      if (!statsSnap.exists()) transaction.set(statsRef, { id: user.uid, xp: 0, gamesPlayed: 0, wins: 0, streak: 0, bestPuzzle: 0 });
      if (!prefsSnap.exists()) transaction.set(prefsRef, { id: user.uid, showOnline: true, showLastSeen: true });
    });
    currentProfile = { id: user.uid, name, username, avatar: initials(name), createdAt: newCreatedAt };
    profileCache.set(user.uid, currentProfile);
    await loadStats(user.uid);
    await loadPrefs(user.uid);
    setAuthView('app');
    renderShell();
    navigate('dashboard', false);
    showToast('Profile saved. Welcome to GCVERSE!', 'success');
  } catch (error) {
    if (error.message === 'USERNAME_TAKEN') setStatus($('#profileStatus'), 'Username not available. Try another one.', 'error');
    else {
      console.error('[GCVERSE] Profile setup failed:', error);
      setStatus($('#profileStatus'), errorText(error, 'Could not save the profile. Check Firestore Rules and try again.'), 'error');
    }
  } finally {
    submit.disabled = false;
    submit.querySelector('span:first-child').textContent = 'Save and enter GCVERSE';
  }
}
async function loadStats(userId) {
  currentStats = { xp: 0, gamesPlayed: 0, wins: 0, streak: 0, bestPuzzle: 0 };
  currentRank = null;
  try {
    const ownSnap = await getDoc(doc(db, 'stats', userId));
    if (ownSnap.exists()) currentStats = { ...currentStats, ...ownSnap.data() };
    const allSnap = await getDocs(collection(db, 'stats'));
    const ranked = allSnap.docs.map(item => ({ id: item.id, xp: Number(item.data().xp || 0) }))
      .sort((a, b) => b.xp - a.xp || a.id.localeCompare(b.id));
    const index = ranked.findIndex(item => item.id === userId);
    currentRank = index >= 0 ? index + 1 : ranked.length + 1;
  } catch (error) {
    console.warn('[GCVERSE] Stats could not be loaded:', error?.code || error?.message || error);
  }
}
async function loadPrefs(userId) {
  try {
    const snap = await getDoc(doc(db, 'userPrefs', userId));
    if (snap.exists()) state.prefs = { showOnline: true, showLastSeen: true, ...snap.data() };
  } catch (error) {
    console.warn('[GCVERSE] Preferences not loaded:', error?.code || error?.message || error);
  }
}
async function handleAuthenticatedUser(user) {
  try {
    setAuthView('auth');
    setStatus($('#authStatus'), 'Loading your profile…');
    const profile = await readOrInitializeProfile(user);
    if (!profile) {
      const userSnap = await getDoc(doc(db, 'users', user.uid)).catch(() => null);
      await showProfileSetup(user, userSnap?.exists() ? userSnap.data() : null);
      return;
    }
    currentProfile = profile;
    profileCache.set(user.uid, profile);
    await Promise.all([loadStats(user.uid), loadPrefs(user.uid)]);
    setAuthView('app');
    renderShell();
    const hashPage = parseHashPage();
    if (hashPage === 'game' && gameInfo[activeGameId]) startGame(activeGameId, false);
    navigate(hashPage || 'dashboard', false);
  } catch (error) {
    console.error('[GCVERSE] Sign-in initialization failed:', error);
    setAuthView('auth');
    setStatus($('#authStatus'), errorText(error, 'We could not load your profile. Check Firestore Rules, then try again.'), 'error');
  }
}
function parseHashPage() {
  const hash = location.hash.replace(/^#/, '');
  if (hash.startsWith('game/')) { activeGameId = hash.slice(5); return 'game'; }
  return hash in pageNames ? hash : 'dashboard';
}
function renderShell() {
  if (!currentProfile) return;
  $('#topbarName').textContent = currentProfile.name;
  $('#topbarAvatar').textContent = initials(currentProfile.name);
  renderPage();
}
function navigate(page, updateHash = true) {
  if (!(page in pageNames) && page !== 'game') page = 'dashboard';
  if (page === 'chats' && activePage !== 'chats') { chatViewMode = 'inbox'; activeChatTab = 'messages'; }
  if (page !== activePage) clearPageListeners();
  activePage = page;
  if (updateHash) {
    const hash = page === 'game' ? `game/${activeGameId}` : page;
    history.replaceState(null, '', `#${hash}`);
  }
  closeMobileSidebar();
  renderPage(true);
}
function updateNavigationState() {
  const navPage = activePage === 'game' ? 'games' : activePage;
  $$('[data-nav]').forEach(button => button.classList.toggle('active', button.dataset.nav === navPage));
  $('#breadcrumbCurrent').textContent = activePage === 'game'
    ? (gameInfo[activeGameId]?.title || coupleGameInfo[activeGameId]?.title || 'Game')
    : (pageNames[activePage] || 'Dashboard');
  const incomingCount = state.incomingRequests.filter(item => item.status === 'pending' && item.recipientId === uid()).length;
  const badge = $('#chatNavBadge');
  if (badge) { badge.textContent = String(incomingCount); badge.classList.toggle('hidden', incomingCount === 0); }
}
function renderPage(rebind = true) {
  if (!currentProfile) return;
  const pageView = $('#pageView');
  const activeElement = pageView.contains(document.activeElement) && document.activeElement !== pageView
    ? document.activeElement
    : null;
  const scrollState = [
    ['.ig-dm-messages', pageView.querySelector('.ig-dm-messages')],
    ['.group-message-list', pageView.querySelector('.group-message-list')]
  ].filter(([, element]) => element).map(([selector, element]) => ({
    selector,
    top: element.scrollTop,
    nearBottom: element.scrollHeight - element.clientHeight - element.scrollTop < 90
  }));
  // Live Firestore snapshots re-render the page. Preserve the active control and
  // caret during those updates so typing a message does not lose focus.
  const focusState = !rebind && activeElement ? {
    id: activeElement.id || '',
    name: activeElement.getAttribute('name') || '',
    tagName: activeElement.tagName,
    dataset: { ...activeElement.dataset },
    selectionStart: typeof activeElement.selectionStart === 'number' ? activeElement.selectionStart : null,
    selectionEnd: typeof activeElement.selectionEnd === 'number' ? activeElement.selectionEnd : null
  } : null;
  const drafts = draftValues();
  if (rebind) clearPageListeners();
  updateNavigationState();
  if (activePage === 'dashboard') pageView.innerHTML = renderDashboard();
  else if (activePage === 'profile') pageView.innerHTML = renderProfilePage();
  else if (activePage === 'games') pageView.innerHTML = renderGamesHub();
  else if (activePage === 'game') pageView.innerHTML = renderGameDetails(activeGameId);
  else if (activePage === 'chats') pageView.innerHTML = renderChats();
  else if (activePage === 'groups') pageView.innerHTML = renderGroups();
  else if (activePage === 'confessions') pageView.innerHTML = renderConfessions();
  else if (activePage === 'couples') pageView.innerHTML = renderCouples();
  else if (activePage === 'ranks') pageView.innerHTML = renderRanks();
  else pageView.innerHTML = `<section class="coming-panel"><h2>Page unavailable</h2><button class="primary-button" data-nav="dashboard" type="button">Back to dashboard</button></section>`;
  restoreDraftValues(drafts);

  // Keep the message viewport stable across live updates. New conversations and
  // views that were already at the bottom open at the latest message; readers
  // who scrolled upward stay at their previous position.
  for (const savedScroll of scrollState) {
    const replacement = pageView.querySelector(savedScroll.selector);
    if (!replacement) continue;
    replacement.scrollTop = savedScroll.nearBottom ? replacement.scrollHeight : savedScroll.top;
  }
  for (const selector of ['.ig-dm-messages', '.group-message-list']) {
    if (pageView.querySelector(selector) && !scrollState.some(item => item.selector === selector)) {
      const container = pageView.querySelector(selector);
      container.scrollTop = container.scrollHeight;
    }
  }

  if (focusState) {
    const all = [...pageView.querySelectorAll('*')];
    let replacement = focusState.id ? all.find(element => element.id === focusState.id) : null;
    if (!replacement && focusState.name) {
      replacement = [...pageView.querySelectorAll('[name]')].find(element =>
        element.tagName === focusState.tagName && element.getAttribute('name') === focusState.name
      ) || null;
    }
    if (!replacement && Object.keys(focusState.dataset).length) {
      replacement = all.find(element => element.tagName === focusState.tagName &&
        Object.entries(focusState.dataset).every(([key, value]) => element.dataset[key] === value)
      ) || null;
    }
    if (replacement) {
      replacement.focus({ preventScroll: true });
      if (focusState.selectionStart !== null && focusState.selectionEnd !== null && typeof replacement.setSelectionRange === 'function') {
        try { replacement.setSelectionRange(focusState.selectionStart, focusState.selectionEnd); } catch { /* unsupported input type */ }
      }
    }
  } else if (rebind) {
    pageView.focus({ preventScroll: true });
  }
  if (rebind) startPageListeners();
}
function renderDashboard() {
  const firstName = escapeHTML(currentProfile.name.split(/\s+/)[0] || currentProfile.name);
  const stats = currentStats || {};
  const cards = [
    { page: 'games', icon: '🎮', title: 'Gaming Hub', description: 'Play puzzles, party prompts and quick challenges.', tag: 'PLAY SOMETHING' },
    { page: 'chats', icon: '💬', title: 'Chats', description: 'Find a homie and message after they accept.', tag: 'YOUR CONNECTIONS' },
    { page: 'groups', icon: '🫂', title: 'Groups / GCs', description: 'Create a GC or join with an invite code.', tag: 'YOUR PEOPLE' },
    { page: 'confessions', icon: '💭', title: 'Confessions', description: 'Post anonymously or under your profile.', tag: 'SAY WHAT YOU FEEL' },
    { page: 'couples', icon: '💞', title: 'Couples Corner', description: 'Invite your partner into a private room.', tag: 'JUST YOU TWO' },
    { page: 'ranks', icon: '🏆', title: 'Ranks', description: 'See real XP and game completion stats.', tag: 'CLIMB TOGETHER' }
  ];
  return `
    <section class="welcome-row"><div><div class="welcome-kicker"><span class="live-dot"></span> YOUR SPACE IS READY</div><h1>What's good, <span class="gradient-text">${firstName}?</span></h1><p>Your people are one tap away. What are we getting into today?</p></div><div class="welcome-chip"><span>✦</span> One space. All your homies.</div></section>
    <section aria-labelledby="quickTitle"><div class="section-heading"><div><span class="section-label">START SOMETHING</span><h2 id="quickTitle">Quick actions</h2><p>Jump straight into your next move.</p></div></div>
      <div class="quick-actions">
        <button class="quick-action" data-nav="games" type="button"><span class="quick-icon">🎮</span><span><strong>Play a game</strong><small>Start a game with its own screen</small></span><span class="quick-arrow">↗</span></button>
        <button class="quick-action" data-nav="chats" type="button"><span class="quick-icon">💬</span><span><strong>Open chats</strong><small>Find accepted connections</small></span><span class="quick-arrow">↗</span></button>
        <button class="quick-action" data-nav="groups" type="button"><span class="quick-icon">＋</span><span><strong>Build your GC</strong><small>Invite your crew with a code</small></span><span class="quick-arrow">↗</span></button>
      </div>
    </section>
    <section aria-labelledby="featuresTitle"><div class="section-heading"><div><span class="section-label">YOUR UNIVERSE</span><h2 id="featuresTitle">Find your corner</h2><p>Six ways to make GCVERSE your own.</p></div></div>
      <div class="feature-grid">${cards.map(card => `<button class="feature-card" type="button" data-nav="${card.page}"><span class="feature-top"><span class="feature-icon">${card.icon}</span><span class="feature-arrow">↗</span></span><h3>${card.title}</h3><p>${card.description}</p><span class="feature-tag">${card.tag}</span></button>`).join('')}</div>
    </section>
    <section class="stats-section" aria-labelledby="statsTitle"><div class="section-heading"><div><span class="section-label">YOUR PROGRESS</span><h2 id="statsTitle">Your stats</h2><p>Updated when a game result is saved.</p></div></div>
      <div class="stats-grid"><div class="stat-card"><span class="stat-icon">✧</span><div><small>Total XP</small><strong>${formatNumber(stats.xp)}</strong></div></div><div class="stat-card"><span class="stat-icon">♜</span><div><small>Current rank</small><strong>${currentRank ? `#${formatNumber(currentRank)}` : '—'}</strong></div></div><div class="stat-card"><span class="stat-icon">🎮</span><div><small>Games played</small><strong>${formatNumber(stats.gamesPlayed)}</strong></div></div></div>
    </section>`;
}
function renderProfilePage() {
  return `<section class="section-page-heading"><div class="page-hero-icon">◎</div><div><h1>Profile & settings</h1><p>Manage your identity and basic privacy preferences.</p></div></section>
    <section class="profile-page-card"><div class="profile-row"><div class="profile-page-avatar">${escapeHTML(initials(currentProfile.name))}</div><div><h2>${escapeHTML(currentProfile.name)}</h2><p>@${escapeHTML(currentProfile.username)}</p></div></div>
      <div class="profile-details"><div class="detail-box"><small>Display name</small><strong>${escapeHTML(currentProfile.name)}</strong></div><div class="detail-box"><small>Username</small><strong>@${escapeHTML(currentProfile.username)}</strong></div><div class="detail-box"><small>XP</small><strong>${formatNumber(currentStats.xp)}</strong></div><div class="detail-box"><small>Authentication</small><strong>Google</strong></div></div>
      <form id="prefsForm" class="form-stack"><h2>Privacy preferences</h2><label class="inline-check"><input type="checkbox" name="showOnline" ${state.prefs.showOnline ? 'checked' : ''}> Show online status (preference saved only)</label><label class="inline-check"><input type="checkbox" name="showLastSeen" ${state.prefs.showLastSeen ? 'checked' : ''}> Show last seen (preference saved only)</label><button class="primary-button" type="submit"><span>Save preferences</span><span>→</span></button></form>
    </section>`;
}
function renderGamesHub() {
  const games = Object.entries(gameInfo).map(([id, game]) => ({ id, ...game, type: gameCategory[id] || 'Game', couple: false }));
  const couples = Object.entries(coupleGameInfo).map(([id, game]) => ({ id, ...game, type: 'Couples room game', couple: true }));
  const allGames = [...games, ...couples];
  const cards = allGames.map(game => `<button class="feature-card" type="button" data-open-game="${escapeHTML(game.id)}" data-couple-game="${game.couple ? 'true' : 'false'}"><span class="feature-top"><span class="feature-icon">${game.icon || '🎮'}</span><span class="feature-arrow">↗</span></span><h3>${escapeHTML(game.title)}</h3><p>${escapeHTML(game.desc)}</p><span class="feature-tag">${escapeHTML(game.type).toUpperCase()}</span></button>`).join('');
  return `<section class="section-page-heading"><div class="page-hero-icon">🎮</div><div><span class="section-label">YOUR NEXT OBSESSION</span><h1>Gaming Hub</h1><p>Open a game to play. Couple games open the private room flow.</p></div></section>
    <div class="section-heading"><div><span class="section-label">GAME LIBRARY</span><h2>Choose a game</h2><p>${allGames.length} preserved game definitions.</p></div></div><div class="feature-grid">${cards}</div>
    <div class="content-note">Solo and local games save results to your profile. Live cross-device party multiplayer still requires a matching multiplayer session schema and deployed Firestore Rules update.</div>`;
}

// Chats: exact username lookup, incoming/outgoing requests, accepted text DMs.
function renderChats() {
  const incoming = state.incomingRequests.filter(item => item.status === 'pending' && item.recipientId === uid());
  const outgoing = state.outgoingRequests.filter(item => ['pending', 'rejected'].includes(item.status));
  const connections = state.connections.filter(item => item.status === 'accepted');
  const selected = connections.find(item => item.id === state.selectedConnectionId) || null;
  if (!selected && connections.length) state.selectedConnectionId = connections[0].id;
  const chosen = connections.find(item => item.id === state.selectedConnectionId) || null;
  const otherId = chosen?.memberIds?.find(id => id !== uid());
  const other = otherId ? profileFor(otherId) : null;
  const messages = state.dmMessages.filter(message => chosen && message.connectionId === chosen.id && (!message.expiresAt || Number(message.expiresAt) > now()))
    .sort((a, b) => Number(a.createdAt || 0) - Number(b.createdAt || 0));

  // Dedicated DM screen: the back button returns to the Instagram-inspired inbox.
  if (chatViewMode === 'conversation' && chosen) {
    return `<section class="ig-dm-screen" aria-label="Conversation with ${escapeHTML(other?.name || 'your homie')}">
      <header class="ig-dm-header">
        <button class="ig-dm-back" type="button" data-action="back-chat-inbox" aria-label="Back to messages">‹</button>
        <span class="ig-avatar ig-dm-avatar">${escapeHTML(initials(other?.name || 'Homie'))}</span>
        <div class="ig-dm-identity"><strong>${escapeHTML(other?.name || 'Homie')}</strong><small>@${escapeHTML(other?.username || 'homie')}</small></div>
        <div class="ig-dm-status">Private chat</div>
      </header>
      <div class="ig-dm-profile-intro"><span class="ig-avatar ig-dm-large-avatar">${escapeHTML(initials(other?.name || 'Homie'))}</span><strong>${escapeHTML(other?.name || 'Homie')}</strong><small>@${escapeHTML(other?.username || 'homie')} · GCVERSE</small><span>You're connected on GCVERSE</span></div>
      <div class="ig-dm-messages" aria-live="polite" aria-label="Messages">
        ${messages.map(message => { const mine = message.fromId === uid(); return `<div class="ig-dm-row ${mine ? 'mine' : 'theirs'}"><div class="ig-dm-bubble"><p>${escapeHTML(message.text)}</p><small>${safeDate(message.createdAt)}</small></div></div>`; }).join('') || '<p class="ig-dm-empty">Say hi and start the conversation.</p>'}
      </div>
      <form id="dmMessageForm" class="ig-dm-composer message-composer"><label class="sr-only" for="dmMessageText">Message</label><button class="ig-composer-symbol" type="button" data-action="focus-message" aria-label="Write a message">＋</button><textarea id="dmMessageText" name="dmMessageText" rows="1" maxlength="1000" placeholder="Message…" required></textarea><button class="ig-send-button" type="submit" aria-label="Send message">Send</button></form>
    </section>`;
  }

  const requestCount = incoming.length;
  const currentTab = ['messages', 'groups', 'requests'].includes(activeChatTab) ? activeChatTab : 'messages';
  const requestsMarkup = `<div class="ig-request-section"><div class="ig-subheading"><h2>Message requests</h2><span>${requestCount} pending</span></div>
      ${incoming.length ? incoming.map(req => { const person = profileFor(req.senderId); return `<div class="ig-request-row"><span class="ig-avatar">${escapeHTML(initials(person.name))}</span><div class="ig-request-copy"><strong>${escapeHTML(person.name)}</strong><small>@${escapeHTML(person.username || 'username unavailable')} wants to connect</small></div><div class="ig-request-actions"><button class="ig-accept-button" type="button" data-action="accept-chat-request" data-request-id="${escapeHTML(req.id)}">Accept</button><button class="ig-reject-button" type="button" data-action="reject-chat-request" data-request-id="${escapeHTML(req.id)}">Delete</button></div></div>`; }).join('') : '<p class="ig-empty-copy">No pending requests. New requests will show up here.</p>'}
      ${outgoing.length ? `<h3 class="ig-outgoing-title">Sent requests</h3>${outgoing.map(req => { const person = profileFor(req.recipientId); return `<div class="ig-request-row"><span class="ig-avatar">${escapeHTML(initials(person.name))}</span><div class="ig-request-copy"><strong>${escapeHTML(person.name)}</strong><small>@${escapeHTML(person.username || 'homie')} · ${escapeHTML(req.status)}</small></div>${req.status === 'rejected' ? `<button class="ig-reject-button" type="button" data-action="retry-chat-request" data-request-id="${escapeHTML(req.id)}">Try again</button>` : ''}</div>`; }).join('')}` : ''}
    </div>`;

  const inboxMarkup = connections.length ? `<div class="ig-inbox-list" aria-label="Your conversations">${connections.map(conn => {
    const person = profileFor(conn.memberIds.find(id => id !== uid()));
    const lastMessage = state.dmMessages.filter(message => message.connectionId === conn.id && (!message.expiresAt || Number(message.expiresAt) > now())).sort((a, b) => Number(b.createdAt || 0) - Number(a.createdAt || 0))[0];
    const preview = lastMessage ? `${lastMessage.fromId === uid() ? 'You: ' : ''}${lastMessage.text}` : `@${person.username || 'homie'} · Start a conversation`;
    const time = lastMessage ? safeDate(lastMessage.createdAt) : '';
    return `<button class="ig-inbox-row" type="button" data-action="select-chat" data-connection-id="${escapeHTML(conn.id)}"><span class="ig-avatar ig-inbox-avatar">${escapeHTML(initials(person.name))}</span><span class="ig-inbox-copy"><strong>${escapeHTML(person.name)}</strong><small>${escapeHTML(preview)}</small></span><span class="ig-inbox-meta">${time ? `<small>${escapeHTML(time)}</small>` : ''}<span class="ig-open-chevron" aria-hidden="true">›</span></span></button>`;
  }).join('')}</div>` : '<div class="ig-inbox-empty"><div class="ig-empty-icon">✉</div><h2>Your messages</h2><p>When you connect with a homie, your conversation will appear here.</p></div>';

  const groupsMarkup = state.groups.length ? `<div class="ig-groups-pane">
      <div class="ig-subheading"><h2>Your groups</h2><span>${state.groups.length} joined</span></div>
      <button class="ig-group-create" type="button" data-nav="groups"><span class="ig-group-create-icon">＋</span><span class="ig-group-create-copy"><strong>Create or join a group</strong><small>Start a GC or use an invite code</small></span><span class="ig-open-chevron">›</span></button>
      <div class="ig-inbox-list" aria-label="Your groups">${state.groups.map(group => `<button class="ig-inbox-row" type="button" data-action="open-group-from-chat" data-group-id="${escapeHTML(group.id)}"><span class="ig-avatar ig-inbox-avatar ig-group-avatar">GC</span><span class="ig-inbox-copy"><strong>${escapeHTML(group.name || 'Your GC')}</strong><small>${(group.memberIds || []).length} member${(group.memberIds || []).length === 1 ? '' : 's'} · Open group chat</small></span><span class="ig-inbox-meta"><span class="ig-open-chevron">›</span></span></button>`).join('')}</div>
    </div>` : `<div class="ig-inbox-empty ig-groups-empty"><div class="ig-empty-icon">♧</div><h2>Your groups</h2><p>You haven’t joined a GC yet. Create one or join your friends with an invite code.</p><button class="ig-group-create-button" type="button" data-nav="groups">Create or join a group <span>→</span></button></div>`;

  return `<section class="ig-chat-page" aria-label="Messages inbox">
    <header class="ig-chat-header"><button class="ig-back-home" type="button" data-nav="dashboard" aria-label="Back to dashboard">‹</button><div class="ig-chat-heading"><h1>Messages</h1><p>One space. All your homies.</p></div><button class="ig-compose-button" type="button" data-action="focus-chat-search" aria-label="Find a homie">＋</button></header>
    <form id="chatSearchForm" class="ig-search-form" role="search"><label class="sr-only" for="chatUsernameSearch">Search exact username</label><span aria-hidden="true">⌕</span><input id="chatUsernameSearch" name="chatUsernameSearch" minlength="3" maxlength="20" placeholder="Search exact username" autocapitalize="none" autocomplete="off" required><button type="submit">Search</button></form>
    <nav class="ig-chat-tabs" aria-label="Message sections"><button class="${currentTab === 'messages' ? 'active' : ''}" type="button" data-action="chat-tab" data-tab="messages" aria-pressed="${currentTab === 'messages'}">Messages</button><button class="${currentTab === 'groups' ? 'active' : ''}" type="button" data-action="chat-tab" data-tab="groups" aria-pressed="${currentTab === 'groups'}">Groups</button><button class="${currentTab === 'requests' ? 'active' : ''}" type="button" data-action="chat-tab" data-tab="requests" aria-pressed="${currentTab === 'requests'}">Requests${requestCount ? `<span class="ig-tab-count">${requestCount}</span>` : ''}</button></nav>
    ${chatSearchResult ? `<div class="ig-search-result"><span class="ig-avatar">${escapeHTML(initials(chatSearchResult.name))}</span><div><strong>${escapeHTML(chatSearchResult.name)}</strong><small>@${escapeHTML(chatSearchResult.username)}</small></div><button class="ig-accept-button" type="button" data-action="send-chat-request" data-user-id="${escapeHTML(chatSearchResult.id)}">Send request</button></div>` : ''}
    ${state.errors.chats ? `<p class="status-message error">${escapeHTML(state.errors.chats)}</p>` : ''}
    ${currentTab === 'requests' ? requestsMarkup : currentTab === 'groups' ? groupsMarkup : inboxMarkup}
  </section>`;
}

// Groups and group text messages.
function renderGroups() {
  const selected = state.groups.find(group => group.id === state.selectedGroupId) || null;
  const messages = [...state.groupMessages].filter(message => !message.expiresAt || Number(message.expiresAt) > now()).sort((a, b) => Number(a.createdAt || 0) - Number(b.createdAt || 0));
  return `<section class="section-page-heading"><div class="page-hero-icon">🫂</div><div><span class="section-label">YOUR PEOPLE</span><h1>Groups / GCs</h1><p>Create a private group or join a crew using its invite code.</p></div></section>
    <section class="profile-page-card"><div class="form-grid"><form id="createGroupForm" class="form-stack"><h2>Create a GC</h2><label for="groupName">Group name</label><input id="groupName" name="groupName" maxlength="40" placeholder="e.g. Homies Forever" required><button class="primary-button" type="submit">Create group</button></form>
      <form id="joinGroupForm" class="form-stack"><h2>Join a GC</h2><label for="groupInviteCode">Invite code</label><input id="groupInviteCode" name="groupInviteCode" minlength="6" maxlength="6" autocapitalize="characters" placeholder="ABC123" required><button class="secondary-button" type="submit">Join with code</button></form></div>
      ${state.errors.groups ? `<p class="status-message error">${escapeHTML(state.errors.groups)}</p>` : ''}
    </section>
    ${selected ? `<section class="profile-page-card"><div class="group-room-head"><div><span class="section-label">YOUR GC</span><h2>${escapeHTML(selected.name)}</h2><p>${(selected.memberIds || []).length} member${(selected.memberIds || []).length === 1 ? '' : 's'} · Invite code <strong>${escapeHTML(selected.inviteCode || '')}</strong></p></div><div class="button-row"><button class="secondary-button" type="button" data-action="copy-group-code" data-code="${escapeHTML(selected.inviteCode || '')}">Copy code</button><button class="secondary-button" type="button" data-action="close-group">Back</button></div></div>
      <div class="chat-message-list group-message-list" aria-live="polite">${messages.map(message => { const mine = message.fromId === uid(); const sender = profileFor(message.fromId); return `<div class="message-row ${mine ? 'mine' : ''}"><div class="message-bubble"><strong>${mine ? 'You' : escapeHTML(message.authorName || sender.name)}</strong><p>${escapeHTML(message.text)}</p><small>${safeDate(message.createdAt)}</small></div></div>`; }).join('') || '<p class="muted-copy">This GC is ready. Send the first message.</p>'}</div>
      <form id="groupMessageForm" class="message-composer"><label class="sr-only" for="groupMessageText">Group message</label><textarea id="groupMessageText" name="groupMessageText" rows="2" maxlength="1000" placeholder="Message your GC…" required></textarea><button class="primary-button" type="submit">Send</button></form>
      <small class="field-help">Group messages are text-only under the current Firestore Rules.</small></section>` : ''}
    <section class="profile-page-card"><div class="section-heading"><div><h2>Your GCs</h2><p>${state.groups.length} group${state.groups.length === 1 ? '' : 's'} joined.</p></div></div>
      ${state.groups.length ? `<div class="feature-grid">${state.groups.map(group => `<button class="feature-card" type="button" data-action="open-group" data-group-id="${escapeHTML(group.id)}"><span class="feature-top"><span class="feature-icon">🫂</span><span class="feature-arrow">↗</span></span><h3>${escapeHTML(group.name)}</h3><p>${(group.memberIds || []).length} members · Code ${escapeHTML(group.inviteCode || '—')}</p><span class="feature-tag">OPEN GC</span></button>`).join('')}</div>` : '<p class="muted-copy">No groups yet. Create one or join with an invite code.</p>'}</section>`;
}

// Confessions: Firestore posts are limited to 24-hour visibility in the UI.
function renderConfessions() {
  const all = [...state.confessions, ...state.groupConfessions]
    .filter(post => Number(post.expiresAt || 0) > now() && !(post.hiddenFor || []).includes(uid()))
    .sort((a, b) => Number(b.createdAt || 0) - Number(a.createdAt || 0));
  const selectedGroup = state.groups.find(group => group.id === state.selectedConfessionGroupId) || null;
  const options = [`<option value="global" ${state.selectedConfessionGroupId === 'global' ? 'selected' : ''}>Global confession</option>`, ...state.groups.map(group => `<option value="${escapeHTML(group.id)}" ${state.selectedConfessionGroupId === group.id ? 'selected' : ''}>GC: ${escapeHTML(group.name)}</option>`)].join('');
  return `<section class="section-page-heading"><div class="page-hero-icon">💭</div><div><span class="section-label">SAY WHAT YOU FEEL</span><h1>Confessions</h1><p>Choose global or one of your GCs. Anonymous posts do not show your identity publicly.</p></div></section>
    <section class="profile-page-card"><form id="confessionForm" class="form-stack"><label for="confessionScope">Post to</label><select id="confessionScope" name="confessionScope">${options}</select><label for="confessionText">Your confession</label><textarea id="confessionText" name="confessionText" rows="4" maxlength="700" minlength="3" placeholder="Get it off your chest…" required></textarea><label class="inline-check"><input type="checkbox" name="confessionAnonymous" checked> Post anonymously</label><button class="primary-button" type="submit">Post confession</button><small class="field-help">Posts are hidden from this feed after 24 hours. True automatic deletion needs a scheduled backend cleanup.</small></form>
      ${state.errors.confessions ? `<p class="status-message error">${escapeHTML(state.errors.confessions)}</p>` : ''}</section>
    <section class="profile-page-card"><div class="section-heading"><div><h2>Recent confessions</h2><p>${all.length} visible post${all.length === 1 ? '' : 's'}${selectedGroup ? ` in ${escapeHTML(selectedGroup.name)}` : ''}.</p></div></div>
      ${all.length ? all.map(post => { const mine = post.authorId === uid(); const ownerName = post.anonymous ? 'Anonymous homie' : profileFor(post.authorId).name; const liked = (post.likes || []).includes(uid()); return `<article class="confession-card"><div class="confession-head"><span class="confession-avatar">${post.anonymous ? '◈' : escapeHTML(initials(ownerName))}</span><div><strong>${escapeHTML(ownerName)}</strong><small>${post.scope === 'gc' ? 'GC confession' : 'Global'} · ${safeDate(post.createdAt)}</small></div><span class="confession-expiry">24h</span></div><p class="confession-content">${escapeHTML(post.content)}</p><div class="button-row"><button class="secondary-button" type="button" data-action="like-confession" data-post-id="${escapeHTML(post.id)}">${liked ? '♥ Liked' : '♡ Like'} · ${(post.likes || []).length}</button><button class="secondary-button" type="button" data-action="report-confession" data-post-id="${escapeHTML(post.id)}">Report</button>${mine && !post.anonymous ? `<button class="secondary-button" type="button" data-action="delete-confession" data-post-id="${escapeHTML(post.id)}">Delete</button>` : ''}</div></article>`; }).join('') : '<p class="muted-copy">No confessions to show yet. You can start the feed.</p>'}</section>`;
}

// Couples Corner: invite-code rooms and private per-round answers.
function renderCouples() {
  const room = state.rooms.find(item => item.id === state.selectedRoomId) || null;
  const gameOptions = Object.entries(coupleGameInfo).map(([id, game]) => `<option value="${id}" ${selectedCoupleGameId === id ? 'selected' : ''}>${escapeHTML(game.title)}</option>`).join('');
  return `<section class="section-page-heading"><div class="page-hero-icon">💞</div><div><span class="section-label">JUST YOU TWO</span><h1>Couples Corner</h1><p>Create a room and share the six-character invite code with your partner.</p></div></section>
    <section class="profile-page-card"><div class="form-grid"><form id="coupleCreateForm" class="form-stack"><h2>Create a private room</h2><label for="coupleGameId">Choose game</label><select id="coupleGameId" name="coupleGameId">${gameOptions}</select><button class="primary-button" type="submit">Create room & code</button></form>
      <form id="coupleJoinForm" class="form-stack"><h2>Join your partner</h2><label for="coupleRoomCode">Partner's code</label><input id="coupleRoomCode" name="coupleRoomCode" minlength="6" maxlength="6" autocapitalize="characters" placeholder="ABC123" required><button class="secondary-button" type="submit">Join room</button></form></div>
      ${state.errors.couples ? `<p class="status-message error">${escapeHTML(state.errors.couples)}</p>` : ''}</section>
    ${room ? renderCoupleRoom(room) : ''}
    <section class="profile-page-card"><div class="section-heading"><div><h2>Your rooms</h2><p>${state.rooms.length} room${state.rooms.length === 1 ? '' : 's'} you can open.</p></div></div>
      ${state.rooms.length ? `<div class="feature-grid">${state.rooms.map(item => { const info = coupleGameInfo[item.gameId] || {}; const joined = (item.memberIds || []).length === 2; return `<button class="feature-card" type="button" data-action="open-couple-room" data-room-id="${escapeHTML(item.id)}"><span class="feature-top"><span class="feature-icon">${info.icon || '💞'}</span><span class="feature-arrow">↗</span></span><h3>${escapeHTML(info.title || 'Couples game')}</h3><p>Code ${escapeHTML(item.code || '—')} · ${joined ? 'Both players joined' : 'Waiting for partner'}</p><span class="feature-tag">${item.completedAt ? 'COMPLETED' : 'OPEN ROOM'}</span></button>`; }).join('')}</div>` : '<p class="muted-copy">No couple rooms yet. Create one to get a code.</p>'}</section>`;
}
function normalizeCoupleQuestion(question) {
  if (Array.isArray(question)) return { category: question[0], q: question[1], freeText: true };
  return question || { q: 'Share an answer.', freeText: true };
}
function renderCoupleRoom(room) {
  const gameId = room.gameId;
  const questions = coupleQuestions[gameId] || [];
  const index = Math.min(Number(room.index || 0), Math.max(questions.length - 1, 0));
  const question = normalizeCoupleQuestion(questions[index]);
  const members = room.memberIds || [];
  const partnerId = members.find(id => id !== uid());
  const partner = partnerId ? profileFor(partnerId) : null;
  const answersReady = members.length === 2 && (room.answeredBy || []).filter(id => members.includes(id)).length === 2;
  const currentAnswer = coupleRoundAnswers[`${room.id}_${index}_${uid()}`];
  const partnerAnswer = partnerId ? coupleRoundAnswers[`${room.id}_${index}_${partnerId}`] : null;
  const options = (question.options || []).map((option, optionIndex) => `<button class="secondary-button option-choice" type="button" data-action="couple-pick-answer" data-option-index="${optionIndex}" data-room-id="${escapeHTML(room.id)}">${escapeHTML(option)}</button>`).join('');
  const completed = Boolean(room.completedAt) || index >= questions.length;
  return `<section class="profile-page-card couple-live-room"><div class="group-room-head"><div><span class="section-label">LIVE ROOM</span><h2>${escapeHTML((coupleGameInfo[gameId] || {}).title || 'Couples game')}</h2><p>Code <strong>${escapeHTML(room.code || '')}</strong> · ${members.length}/2 players${partner ? ` · Partner: ${escapeHTML(partner.name)}` : ''}</p></div><div class="button-row"><button class="secondary-button" type="button" data-action="copy-couple-code" data-code="${escapeHTML(room.code || '')}">Copy code</button><button class="secondary-button" type="button" data-action="close-couple-room">Close</button></div></div>
    ${members.length < 2 ? '<div class="content-note">Share the code with your partner. The game unlocks once the second person joins.</div>' : completed ? `<div class="game-result"><span class="page-hero-icon">💗</span><h3>You finished this room!</h3><p>Both players completed the questions. Create a new room to play again.</p></div>` : `<div class="game-question"><span class="section-label">ROUND ${index + 1} OF ${questions.length}</span>${question.category ? `<p class="feature-tag">${escapeHTML(question.category)}</p>` : ''}<h3>${escapeHTML(question.q || 'Choose an answer')}</h3>${question.display ? `<p class="puzzle-display">${escapeHTML(question.display)}</p>` : ''}
    ${currentAnswer ? `<div class="content-note"><strong>Your answer:</strong> ${escapeHTML(currentAnswer.answer)}<br>${answersReady && partnerAnswer ? `<strong>${escapeHTML(partner?.name || 'Partner')}:</strong> ${escapeHTML(partnerAnswer.answer)}` : 'Waiting for your partner to answer this round. Answers stay private until both people answer.'}</div>` : question.freeText || !question.options ? `<form id="coupleAnswerForm" class="form-stack"><label for="coupleFreeAnswer">Your answer</label><textarea id="coupleFreeAnswer" name="coupleFreeAnswer" maxlength="1000" rows="3" required placeholder="Your answer is only revealed after both submit…"></textarea><button class="primary-button" type="submit">Submit answer</button></form>` : `<div class="button-row options-grid">${options}</div>`}
    ${answersReady ? `<button class="primary-button" type="button" data-action="next-couple-round" data-room-id="${escapeHTML(room.id)}">${index === questions.length - 1 ? 'Finish room' : 'Next question'} →</button>` : ''}</div>`}</section>`;
}

function renderRanks() {
  return `<section class="section-page-heading"><div class="page-hero-icon">🏆</div><div><span class="section-label">THE LEADERBOARD</span><h1>Ranks</h1><p>Leaderboard names are loaded by exact profile lookups; totals come from stored stats.</p></div></section>
    <section class="profile-page-card"><div class="section-heading"><div><h2>Top homies</h2><p>${state.rankEntries.length} profiles with saved stats.</p></div><button class="secondary-button" type="button" data-action="refresh-ranks">Refresh</button></div>
    ${state.rankLoading ? '<p class="muted-copy">Loading ranks…</p>' : state.errors.ranks ? `<p class="status-message error">${escapeHTML(state.errors.ranks)}</p>` : state.rankEntries.length ? `<div class="rank-list">${state.rankEntries.map((entry, index) => `<div class="rank-row ${entry.id === uid() ? 'is-self' : ''}"><span class="rank-position">#${index + 1}</span><span class="profile-page-avatar">${escapeHTML(initials(entry.name))}</span><div class="rank-person"><strong>${escapeHTML(entry.name)} ${entry.id === uid() ? '<small>(you)</small>' : ''}</strong><small>${entry.username ? `@${escapeHTML(entry.username)} · ` : ''}${formatNumber(entry.gamesPlayed)} games · ${formatNumber(entry.wins)} wins</small></div><strong class="rank-xp">${formatNumber(entry.xp)} XP</strong></div>`).join('')}</div>` : '<p class="muted-copy">No rank stats are available yet.</p>'}</section>`;
}

// The game engines use the supplied content and save results to Firestore.
function startGame(gameId, doNavigate = true) {
  activeGameId = gameId;
  if (coupleGameInfo[gameId]) {
    selectedCoupleGameId = gameId;
    if (doNavigate) navigate('couples');
    return;
  }
  const run = { id: gameId, index: 0, score: 0, answers: [], finished: false, saved: false, selected: null, used: [], traits: {}, board: Array(9).fill(''), turn: 'X', winner: '', explanation: '', revealed: false };
  if (gameId === 'truth') run.prompt = truthPrompts[Math.floor(Math.random() * truthPrompts.length)];
  if (gameId === 'redflag') run.scenarios = shuffle(redFlagScenarios);
  if (gameId === 'challenge') { run.prompts = shuffle(challengePrompts); run.prompt = run.prompts[0]?.text || String(run.prompts[0] || ''); }
  if (gameId === 'puzzle') run.questions = shuffle(puzzleQuestions);
  gameRun = run;
  if (doNavigate) navigate('game');
}
function renderGameDetails(gameId) {
  const game = gameInfo[gameId];
  if (!game) return `<section class="coming-panel"><div><h2>Game not found</h2><p>This identifier isn't in the game catalogue.</p><button class="primary-button" type="button" data-nav="games">Back to Gaming Hub</button></div></section>`;
  if (!gameRun || gameRun.id !== gameId) startGame(gameId, false);
  const run = gameRun;
  if (gameId === 'truth') return renderTruthGame(game, run);
  if (gameId === 'redflag') return renderRedFlagGame(game, run);
  if (gameId === 'challenge') return renderChallengeGame(game, run);
  if (gameId === 'tmkoc') return renderTMKOCGame(game, run);
  if (gameId === 'xo') return renderXOGame(game, run);
  if (gameId === 'puzzle') return renderPuzzleGame(game, run);
  return `<section class="coming-panel"><h2>${escapeHTML(game.title)}</h2><p>This game does not have a client engine yet.</p></section>`;
}
function gameHero(game) {
  return `<section class="section-page-heading"><div class="page-hero-icon">${game.icon || '🎮'}</div><div><span class="section-label">PLAYABLE GAME</span><h1>${escapeHTML(game.title)}</h1><p>${escapeHTML(game.desc)}</p></div></section>`;
}
function renderTruthGame(game, run) {
  const prompt = run.prompt || truthPrompts[0];
  return `${gameHero(game)}<section class="profile-page-card game-panel"><span class="section-label">TRUTH OR DARE</span><h2>Here's your prompt</h2><p class="game-prompt">${escapeHTML(prompt)}</p><div class="button-row"><button class="primary-button" data-action="truth-next" data-kind="truth" type="button">Next truth</button><button class="secondary-button" data-action="truth-next" data-kind="dare" type="button">Give me a dare</button><button class="secondary-button" data-action="truth-next" data-kind="random" type="button">Surprise me</button></div><p class="field-help">This mode is playable on this device. Cross-device turn syncing still needs the multiplayer schema update.</p><div class="button-row"><button class="primary-button" type="button" data-action="finish-game">Finish & save result</button><button class="secondary-button" type="button" data-nav="games">Exit game</button></div></section>`;
}
function renderRedFlagGame(game, run) {
  if (run.finished) return `${gameHero(game)}<section class="profile-page-card game-result"><h2>Round complete 🚩</h2><p>You judged ${run.answers.length} scenarios. There is no universal right answer—use the explanations to discuss boundaries.</p><button class="primary-button" type="button" data-action="finish-game">Save result</button><button class="secondary-button" type="button" data-nav="games">Back to games</button></section>`;
  const scenario = run.scenarios[run.index];
  return `${gameHero(game)}<section class="profile-page-card game-panel"><span class="section-label">SCENARIO ${run.index + 1} OF ${run.scenarios.length}</span><p class="feature-tag">${escapeHTML(scenario.area)}</p><h2>What's your verdict?</h2><p class="game-prompt">${escapeHTML(scenario.text)}</p><div class="button-row options-grid"><button class="primary-button" type="button" data-action="redflag-vote" data-vote="green">🟢 Green flag</button><button class="secondary-button" type="button" data-action="redflag-vote" data-vote="depends">🟡 Depends</button><button class="secondary-button" type="button" data-action="redflag-vote" data-vote="red">🔴 Red flag</button></div><p class="field-help">Your answers are a conversation starter, not a diagnosis of a relationship.</p></section>`;
}
function renderChallengeGame(game, run) {
  if (run.finished) return `${gameHero(game)}<section class="profile-page-card game-result"><h2>Challenge run complete 🎲</h2><p>You completed ${run.answers.length} prompts and earned ${run.score} points.</p><button class="primary-button" type="button" data-action="finish-game">Save result</button><button class="secondary-button" type="button" data-nav="games">Back to games</button></section>`;
  const item = run.prompts[Math.min(run.index, run.prompts.length - 1)];
  const prompt = typeof item === 'string' ? item : item?.text || String(item || '');
  return `${gameHero(game)}<section class="profile-page-card game-panel"><span class="section-label">CHALLENGE ${run.index + 1} OF 4</span><p class="feature-tag">${escapeHTML(typeof item === 'string' ? 'Surprise' : item?.category || 'Challenge')} · ${escapeHTML(typeof item === 'string' ? '' : item?.difficulty || '')}</p><p class="game-prompt">${escapeHTML(prompt)}</p><div class="button-row"><button class="primary-button" type="button" data-action="complete-challenge">Done — next challenge</button><button class="secondary-button" type="button" data-action="finish-game">Finish early</button></div></section>`;
}
function renderTMKOCGame(game, run) {
  if (run.finished) {
    const character = run.character || tmkocCharacters[0];
    return `${gameHero(game)}<section class="profile-page-card game-result"><div class="page-hero-icon">${character.emoji}</div><h2>You got ${escapeHTML(character.name)}!</h2><p>${escapeHTML(character.quote)}</p><div class="profile-details">${Object.entries(character.traits || {}).map(([trait, value]) => `<div class="detail-box"><small>${escapeHTML(trait)}</small><strong>${formatNumber(value)}%</strong></div>`).join('')}</div><button class="primary-button" type="button" data-action="save-tmkoc-result">Save result</button><button class="secondary-button" type="button" data-action="restart-game">Play again</button></section>`;
  }
  const question = tmkocQuestions[run.index];
  return `${gameHero(game)}<section class="profile-page-card game-panel"><span class="section-label">QUESTION ${run.index + 1} OF ${tmkocQuestions.length}</span><h2>${escapeHTML(question.q)}</h2><div class="button-column">${question.options.map((option, index) => `<button class="secondary-button" type="button" data-action="tmkoc-answer" data-option-index="${index}">${escapeHTML(option.t)}</button>`).join('')}</div></section>`;
}
function checkXO(board) {
  const lines = [[0,1,2],[3,4,5],[6,7,8],[0,3,6],[1,4,7],[2,5,8],[0,4,8],[2,4,6]];
  for (const [a,b,c] of lines) if (board[a] && board[a] === board[b] && board[b] === board[c]) return board[a];
  return board.every(Boolean) ? 'draw' : '';
}
function renderXOGame(game, run) {
  const done = Boolean(run.winner);
  const status = !done ? `${run.turn === 'X' ? 'Your turn (X)' : 'Computer thinking (O)'}` : run.winner === 'draw' ? 'It is a draw!' : run.winner === 'X' ? 'You win! 🎉' : 'Computer wins this round.';
  return `${gameHero(game)}<section class="profile-page-card game-panel"><span class="section-label">VS COMPUTER · LOCAL BOARD</span><h2>${escapeHTML(status)}</h2><div class="xo-board">${run.board.map((cell, index) => `<button class="xo-cell" type="button" data-action="xo-move" data-cell-index="${index}" ${cell || done ? 'disabled' : ''} aria-label="Cell ${index + 1}">${escapeHTML(cell)}</button>`).join('')}</div>${done ? `<div class="button-row"><button class="primary-button" type="button" data-action="save-xo-result">Save result</button><button class="secondary-button" type="button" data-action="restart-game">Play again</button></div>` : '<p class="field-help">Cross-device two-player matchmaking is not enabled by the current session rules.</p>'}</section>`;
}
function renderPuzzleGame(game, run) {
  const question = run.questions[run.index];
  if (!question) return `${gameHero(game)}<section class="profile-page-card game-result"><h2>Puzzle run complete 🧩</h2><p>Score: ${run.score}/${run.questions.length * 10} points.</p><button class="primary-button" type="button" data-action="finish-game">Save result</button><button class="secondary-button" type="button" data-action="restart-game">Play again</button></section>`;
  const correct = run.selected === question.answer;
  return `${gameHero(game)}<section class="profile-page-card game-panel"><span class="section-label">PUZZLE ${run.index + 1} OF ${run.questions.length}</span><h2>${escapeHTML(question.q)}</h2><p class="puzzle-display">${escapeHTML(question.display)}</p><div class="button-column">${question.options.map(option => `<button class="secondary-button ${run.revealed && option === question.answer ? 'correct-answer' : ''}" type="button" data-action="puzzle-select" data-answer="${escapeHTML(option)}" ${run.revealed ? 'disabled' : ''}>${escapeHTML(option)}</button>`).join('')}</div>
    ${run.revealed ? `<div class="content-note">${run.selected === question.answer ? '✅ Correct!' : `❌ Correct answer: ${escapeHTML(question.answer)}`} ${escapeHTML(question.explain)}</div><div class="button-row"><button class="primary-button" type="button" data-action="puzzle-next">${run.index === run.questions.length - 1 ? 'Finish run' : 'Next puzzle'} →</button></div>` : `<button class="primary-button" type="button" data-action="puzzle-check" ${run.selected === null ? 'disabled' : ''}>Check answer</button>`}</section>`;
}
async function saveGameResult(gameId, score, won, result = {}) {
  if (!uid() || !currentProfile) throw new Error('Sign in to save your progress.');
  const sessionRef = doc(collection(db, 'gameSessions'));
  const statsRef = doc(db, 'stats', uid());
  const stamp = now();
  await runTransaction(db, async transaction => {
    const statsSnap = await transaction.get(statsRef);
    const base = statsSnap.exists() ? statsSnap.data() : { id: uid(), xp: 0, gamesPlayed: 0, wins: 0, streak: 0, bestPuzzle: 0 };
    const next = {
      id: uid(),
      xp: Math.max(0, Number(base.xp || 0)) + Math.max(0, Number(score || 0)),
      gamesPlayed: Math.max(0, Number(base.gamesPlayed || 0)) + 1,
      wins: Math.max(0, Number(base.wins || 0)) + (won ? 1 : 0),
      streak: won ? Math.max(0, Number(base.streak || 0)) + 1 : 0,
      bestPuzzle: gameId === 'puzzle' ? Math.max(Number(base.bestPuzzle || 0), Number(score || 0)) : Math.max(0, Number(base.bestPuzzle || 0))
    };
    transaction.set(statsRef, next);
    transaction.set(sessionRef, {
      id: sessionRef.id, userId: uid(), userIds: [uid()], gameId,
      score: Math.max(0, Number(score || 0)), won: Boolean(won), result,
      createdAt: stamp, expiresAt: stamp + 365 * 24 * 60 * 60 * 1000
    });
  });
  currentStats = { ...currentStats, xp: currentStats.xp + Math.max(0, Number(score || 0)), gamesPlayed: currentStats.gamesPlayed + 1, wins: currentStats.wins + (won ? 1 : 0), streak: won ? currentStats.streak + 1 : 0, bestPuzzle: gameId === 'puzzle' ? Math.max(currentStats.bestPuzzle, Number(score || 0)) : currentStats.bestPuzzle };
  showToast(`Result saved · +${formatNumber(score)} XP`, 'success');
}
async function finishCurrentGame({ won = false, result = {} } = {}) {
  if (!gameRun || gameRun.saved) return;
  gameRun.saved = true;
  try {
    await saveGameResult(gameRun.id, gameRun.score || 0, won, { answers: gameRun.answers || [], ...result });
    await loadStats(uid());
  } catch (error) {
    gameRun.saved = false;
    console.error('[GCVERSE] Saving game result failed:', error);
    showToast(errorText(error, 'Could not save this game result.'), 'error');
  }
  renderPage(false);
}

// Page subscriptions are cleared on navigation and reused while a page stays open.
function startPageListeners() {
  if (!uid()) return;
  if (activePage === 'chats') {
    listen(query(collection(db, 'chatConnections'), where('memberIds', 'array-contains', uid()), limit(100)), snap => {
      state.errors.chats = '';
      state.connections = snap.docs.map(item => ({ ...item.data(), id: item.id }));
      void cacheProfiles(state.connections.flatMap(item => item.memberIds || [])).then(() => reRenderPage());
      reRenderPage();
    }, 'chats');
    listen(query(collection(db, 'chatRequests'), where('recipientId', '==', uid()), limit(100)), snap => {
      state.incomingRequests = snap.docs.map(item => ({ ...item.data(), id: item.id }));
      void cacheProfiles(state.incomingRequests.map(item => item.senderId)).then(() => reRenderPage());
      reRenderPage();
    }, 'chats');
    listen(query(collection(db, 'chatRequests'), where('senderId', '==', uid()), limit(100)), snap => {
      state.outgoingRequests = snap.docs.map(item => ({ ...item.data(), id: item.id }));
      void cacheProfiles(state.outgoingRequests.map(item => item.recipientId)).then(() => reRenderPage());
      reRenderPage();
    }, 'chats');
    listen(query(collection(db, 'dmMessages'), where('memberIds', 'array-contains', uid()), limit(200)), snap => {
      state.dmMessages = snap.docs.map(item => ({ ...item.data(), id: item.id }));
      reRenderPage();
    }, 'chats');
    listen(query(collection(db, 'gcs'), where('memberIds', 'array-contains', uid()), limit(100)), snap => {
      state.errors.chats = '';
      state.groups = snap.docs.map(item => ({ ...item.data(), id: item.id }));
      void cacheProfiles(state.groups.flatMap(group => group.memberIds || [])).then(() => reRenderPage());
      reRenderPage();
    }, 'chats');
  } else if (activePage === 'groups') {
    listen(query(collection(db, 'gcs'), where('memberIds', 'array-contains', uid()), limit(100)), snap => {
      state.errors.groups = '';
      state.groups = snap.docs.map(item => ({ ...item.data(), id: item.id }));
      void cacheProfiles(state.groups.flatMap(group => group.memberIds || [])).then(() => reRenderPage());
      reRenderPage();
    }, 'groups');
    if (state.selectedGroupId) listen(query(collection(db, 'messages'), where('gcId', '==', state.selectedGroupId), limit(150)), snap => {
      state.groupMessages = snap.docs.map(item => ({ ...item.data(), id: item.id }));
      void cacheProfiles(state.groupMessages.map(item => item.fromId)).then(() => reRenderPage());
      reRenderPage();
    }, 'groups');
  } else if (activePage === 'confessions') {
    listen(query(collection(db, 'confessions'), where('scope', '==', 'global'), limit(100)), snap => {
      state.errors.confessions = '';
      state.confessions = snap.docs.map(item => ({ ...item.data(), id: item.id }));
      reRenderPage();
    }, 'confessions');
    listen(query(collection(db, 'gcs'), where('memberIds', 'array-contains', uid()), limit(100)), snap => {
      state.groups = snap.docs.map(item => ({ ...item.data(), id: item.id }));
      reRenderPage();
    }, 'confessions');
    if (state.selectedConfessionGroupId !== 'global') {
      listen(query(collection(db, 'confessions'), where('gcId', '==', state.selectedConfessionGroupId), limit(100)), groupSnap => {
        state.errors.confessions = '';
        state.groupConfessions = groupSnap.docs.map(item => ({ ...item.data(), id: item.id }));
        reRenderPage();
      }, 'confessions');
    } else state.groupConfessions = [];
  } else if (activePage === 'ranks') {
    void loadRanks();
  } else if (activePage === 'couples') {
    listen(query(collection(db, 'coupleRooms'), where('memberIds', 'array-contains', uid()), limit(100)), snap => {
      state.rooms = snap.docs.map(item => ({ ...item.data(), id: item.id }));
      void cacheProfiles(state.rooms.flatMap(room => room.memberIds || [])).then(() => reRenderPage());
      reRenderPage();
      const room = state.rooms.find(item => item.id === state.selectedRoomId);
      if (room && (room.memberIds || []).length === 2 && !room.completedAt) void loadCoupleRoundAnswers(room);
    }, 'couples');
  }
}
async function loadCoupleRoundAnswers(room) {
  const members = room.memberIds || [];
  if (members.length !== 2) return;
  const index = Number(room.index || 0);
  const roundKey = String(index);
  const ready = (room.answeredBy || []).filter(id => members.includes(id)).length === 2;
  // Load the current user's own answer even while waiting; Firestore Rules hide the partner's answer.
  const ownId = `${room.id}_${roundKey}_${uid()}`;
  try {
    const ownSnap = await getDoc(doc(db, 'coupleAnswers', ownId));
    if (ownSnap.exists()) coupleRoundAnswers[`${room.id}_${index}_${uid()}`] = ownSnap.data();
  } catch (error) {
    console.warn('[GCVERSE] Own couple answer not loaded:', error?.code || error?.message || error);
  }
  if (ready) {
    for (const memberId of members.filter(id => id !== uid())) {
      const answerId = `${room.id}_${roundKey}_${memberId}`;
      try {
        const snap = await getDoc(doc(db, 'coupleAnswers', answerId));
        if (snap.exists()) coupleRoundAnswers[`${room.id}_${index}_${memberId}`] = snap.data();
      } catch (error) {
        // The rules intentionally prevent viewing a partner's answer until both exist.
        console.warn('[GCVERSE] Partner answer not visible yet:', error?.code || error?.message || error);
      }
    }
  }
  reRenderPage();
}
async function loadRanks() {
  state.rankLoading = true;
  state.errors.ranks = '';
  reRenderPage();
  try {
    const snap = await getDocs(query(collection(db, 'stats'), limit(100)));
    const raw = snap.docs.map(item => ({ id: item.id, ...item.data() }))
      .sort((a, b) => Number(b.xp || 0) - Number(a.xp || 0) || a.id.localeCompare(b.id)).slice(0, 30);
    await cacheProfiles(raw.map(item => item.id));
    state.rankEntries = raw.map(item => {
      const person = profileFor(item.id);
      return { id: item.id, name: person.name, username: person.username, xp: Number(item.xp || 0), gamesPlayed: Number(item.gamesPlayed || 0), wins: Number(item.wins || 0) };
    });
  } catch (error) {
    console.error('[GCVERSE] Ranks failed:', error);
    state.errors.ranks = errorText(error, 'Could not load ranks.');
  } finally {
    state.rankLoading = false;
    reRenderPage();
  }
}

// Action handlers
async function searchChatUsername(form) {
  const username = normalizeUsername(form.get('chatUsernameSearch') || '');
  if (!isValidUsername(username)) throw new Error('Enter a valid exact username (3–20 characters).');
  const indexSnap = await getDoc(doc(db, 'usernames', username));
  if (!indexSnap.exists()) { chatSearchResult = null; reRenderPage(); showToast('No homie found with that exact username.', ''); return; }
  const targetId = indexSnap.data().userId;
  if (!targetId || targetId === uid()) { chatSearchResult = null; reRenderPage(); showToast(targetId === uid() ? 'That is your own username.' : 'That username is unavailable.', ''); return; }
  const profileSnap = await getDoc(doc(db, 'users', targetId));
  if (!profileSnap.exists()) throw new Error('The profile for this username is not available.');
  chatSearchResult = { ...profileSnap.data(), id: targetId };
  profileCache.set(targetId, chatSearchResult);
  reRenderPage();
}
async function sendChatRequest(targetId) {
  if (!targetId || targetId === uid()) throw new Error('Choose another user.');
  const requestId = `${uid()}__to__${targetId}`;
  const requestRef = doc(db, 'chatRequests', requestId);
  const existing = await getDoc(requestRef);
  const stamp = now();
  if (existing.exists()) {
    const data = existing.data();
    if (data.status === 'accepted') { showToast('You are already connected.', 'success'); return; }
    if (data.status === 'pending') { showToast('Your request is already pending.', ''); return; }
    if (data.status === 'rejected' && data.senderId === uid()) {
      await updateDoc(requestRef, { status: 'pending', createdAt: stamp, respondedAt: null, respondedBy: null });
      showToast('Request sent again.', 'success');
      return;
    }
    throw new Error('A request already exists. The other person can start a new request back.');
  }
  await setDoc(requestRef, {
    id: requestId, senderId: uid(), recipientId: targetId, type: 'personal', status: 'pending',
    memberIds: [uid(), targetId], createdAt: stamp, respondedAt: null, respondedBy: null
  });
  showToast('Chat request sent.', 'success');
}
async function respondChatRequest(requestId, accepted) {
  const requestRef = doc(db, 'chatRequests', requestId);
  const snap = await getDoc(requestRef);
  if (!snap.exists()) throw new Error('This request no longer exists.');
  const data = snap.data();
  if (data.recipientId !== uid() || data.status !== 'pending') throw new Error('This request is no longer pending for your account.');
  const stamp = now();
  const connectionId = sortedPairId(data.senderId, data.recipientId);
  await runTransaction(db, async transaction => {
    const latest = await transaction.get(requestRef);
    const connectionRef = doc(db, 'chatConnections', connectionId);
    const connectionSnap = await transaction.get(connectionRef);
    if (!latest.exists() || latest.data().status !== 'pending' || latest.data().recipientId !== uid()) throw new Error('REQUEST_CHANGED');
    transaction.update(requestRef, { status: accepted ? 'accepted' : 'rejected', respondedAt: stamp, respondedBy: uid() });
    if (accepted && !connectionSnap.exists()) {
      transaction.set(connectionRef, { id: connectionId, status: 'accepted', acceptedBy: uid(), memberIds: [data.senderId, data.recipientId].sort(), requestId, createdAt: stamp });
    }
  });
  if (accepted) state.selectedConnectionId = connectionId;
  showToast(accepted ? 'Chat request accepted.' : 'Request rejected.', accepted ? 'success' : '');
  renderPage(true);
}
async function sendDM(form) {
  const text = String(form.get('dmMessageText') || '').trim();
  const connection = state.connections.find(item => item.id === state.selectedConnectionId && item.status === 'accepted');
  if (!connection) throw new Error('Select an accepted chat first.');
  if (!text || text.length > 1000) throw new Error('Message must be between 1 and 1000 characters.');
  const targetId = connection.memberIds.find(id => id !== uid());
  const messageRef = doc(collection(db, 'dmMessages'));
  const stamp = now();
  await setDoc(messageRef, {
    id: messageRef.id, type: 'dm', fromId: uid(), toId: targetId, connectionId: connection.id,
    memberIds: [...connection.memberIds], text, createdAt: stamp, expiresAt: stamp + MESSAGE_LIFETIME_MS
  });
  form.reset();
}
async function createGroup(form) {
  const name = String(form.get('groupName') || '').trim().replace(/\s+/g, ' ');
  if (name.length < 2 || name.length > 40) throw new Error('Group name must be between 2 and 40 characters.');
  const groupRef = doc(collection(db, 'gcs'));
  let code = randomCode();
  for (let tries = 0; tries < 5 && (await getDoc(doc(db, 'gcInvites', code))).exists(); tries++) code = randomCode();
  const stamp = now();
  const member = activeUserSummary();
  const batch = writeBatch(db);
  batch.set(groupRef, { id: groupRef.id, name, ownerId: uid(), memberIds: [uid()], members: [member], inviteCode: code, createdAt: stamp, gamesPlayed: 0, lastPlayedAt: stamp });
  batch.set(doc(db, 'gcInvites', code), { id: code, ownerId: uid(), gcId: groupRef.id, createdAt: stamp });
  await batch.commit();
  state.selectedGroupId = groupRef.id;
  state.groupMessages = [];
  showToast(`GC created. Invite code: ${code}`, 'success');
  form.reset();
  renderPage(true);
}
async function joinGroup(form) {
  const code = String(form.get('groupInviteCode') || '').trim().toUpperCase();
  if (!/^[A-HJ-NP-Z2-9]{6}$/.test(code)) throw new Error('Enter the 6-character invite code.');
  const inviteSnap = await getDoc(doc(db, 'gcInvites', code));
  if (!inviteSnap.exists()) throw new Error('That invite code was not found.');
  const groupId = inviteSnap.data().gcId;
  const groupRef = doc(db, 'gcs', groupId);
  const groupSnap = await getDoc(groupRef);
  if (!groupSnap.exists()) throw new Error('This group no longer exists.');
  const group = groupSnap.data();
  if ((group.memberIds || []).includes(uid())) { state.selectedGroupId = groupId; renderPage(true); showToast('You are already in this GC.', ''); return; }
  const member = activeUserSummary();
  await updateDoc(groupRef, { memberIds: [...(group.memberIds || []), uid()], members: [...(group.members || []), member] });
  state.selectedGroupId = groupId;
  form.reset();
  showToast(`Joined ${group.name}.`, 'success');
  renderPage(true);
}
async function sendGroupMessage(form) {
  const text = String(form.get('groupMessageText') || '').trim();
  if (!text || text.length > 1000) throw new Error('Message must be between 1 and 1000 characters.');
  const group = state.groups.find(item => item.id === state.selectedGroupId);
  if (!group || !(group.memberIds || []).includes(uid())) throw new Error('Choose a GC you belong to.');
  const messageRef = doc(collection(db, 'messages'));
  const stamp = now();
  await setDoc(messageRef, {
    id: messageRef.id, type: 'gc', gcId: group.id, memberIds: [...group.memberIds],
    fromId: uid(), authorName: currentProfile.name, text, createdAt: stamp, expiresAt: stamp + MESSAGE_LIFETIME_MS
  });
  const liveInput = $('#groupMessageText');
  if (liveInput) liveInput.value = '';
}
async function createConfession(form) {
  const content = String(form.get('confessionText') || '').trim();
  const anonymous = Boolean(form.get('confessionAnonymous'));
  const scopeId = String(form.get('confessionScope') || 'global');
  if (content.length < 3 || content.length > 700) throw new Error('Confessions must be between 3 and 700 characters.');
  const isGlobal = scopeId === 'global';
  const group = !isGlobal ? state.groups.find(item => item.id === scopeId) : null;
  if (!isGlobal && (!group || !(group.memberIds || []).includes(uid()))) throw new Error('Join that GC before posting a group confession.');
  const postRef = doc(collection(db, 'confessions'));
  const stamp = now();
  const expiresAt = stamp + CONFESSION_LIFETIME_MS;
  const post = {
    id: postRef.id, content, createdAt: stamp, expiresAt, anonymous,
    authorId: anonymous ? null : uid(), scope: isGlobal ? 'global' : 'gc', gcId: isGlobal ? null : group.id,
    likes: [], reports: [], hiddenFor: []
  };
  const batch = writeBatch(db);
  batch.set(postRef, isGlobal ? post : { ...post, memberIds: [...group.memberIds] });
  if (anonymous) batch.set(doc(db, 'confessionOwners', postRef.id), { id: postRef.id, postId: postRef.id, authorId: uid(), expiresAt });
  await batch.commit();
  const liveText = $('#confessionText');
  if (liveText) liveText.value = '';
  const liveAnonymous = $('[name=confessionAnonymous]');
  if (liveAnonymous) liveAnonymous.checked = true;
  state.selectedConfessionGroupId = scopeId;
  showToast('Confession posted.', 'success');
}
async function likeConfession(postId) {
  await updateDoc(doc(db, 'confessions', postId), { likes: arrayUnion(uid()) });
}
async function reportConfession(postId) {
  await updateDoc(doc(db, 'confessions', postId), { reports: arrayUnion(uid()) });
  showToast('Report submitted. Moderation review tools are not yet connected to an admin queue.', 'success');
}
async function deleteConfession(postId) {
  const post = [...state.confessions, ...state.groupConfessions].find(item => item.id === postId);
  if (!post || post.authorId !== uid() || post.anonymous) throw new Error('You can only delete a confession you posted under your profile.');
  await deleteDoc(doc(db, 'confessions', postId));
  showToast('Confession deleted.', 'success');
}

// Couples room creation/joining and synchronized answer rounds.
async function createCoupleRoom(form) {
  const gameId = String(form.get('coupleGameId') || selectedCoupleGameId);
  if (!coupleGameInfo[gameId]) throw new Error('Choose a valid couples game.');
  let code = randomCode();
  for (let tries = 0; tries < 5 && (await getDoc(doc(db, 'coupleRoomCodes', code))).exists(); tries++) code = randomCode();
  const roomRef = doc(collection(db, 'coupleRooms'));
  const stamp = now();
  const batch = writeBatch(db);
  batch.set(roomRef, { id: roomRef.id, ownerId: uid(), partnerId: '', memberIds: [uid()], code, gameId, index: 0, answeredBy: [], createdAt: stamp, expiresAt: stamp + 7 * 24 * 60 * 60 * 1000, completedAt: null });
  batch.set(doc(db, 'coupleRoomCodes', code), { id: code, ownerId: uid(), roomId: roomRef.id, createdAt: stamp });
  await batch.commit();
  selectedCoupleGameId = gameId;
  state.selectedRoomId = roomRef.id;
  coupleRoundAnswers = {};
  form.reset();
  showToast(`Room created. Share code ${code} with your partner.`, 'success');
  renderPage(true);
}
async function joinCoupleRoom(form) {
  const code = String(form.get('coupleRoomCode') || '').trim().toUpperCase();
  if (!/^[A-HJ-NP-Z2-9]{6}$/.test(code)) throw new Error('Enter the six-character room code.');
  const codeSnap = await getDoc(doc(db, 'coupleRoomCodes', code));
  if (!codeSnap.exists()) throw new Error('That room code was not found.');
  const roomRef = doc(db, 'coupleRooms', codeSnap.data().roomId);
  const roomSnap = await getDoc(roomRef);
  if (!roomSnap.exists()) throw new Error('That room no longer exists.');
  const room = roomSnap.data();
  if (Number(room.expiresAt || 0) < now()) throw new Error('This room code has expired. Create a new one.');
  if ((room.memberIds || []).includes(uid())) {
    state.selectedRoomId = room.id;
    selectedCoupleGameId = room.gameId;
  } else {
    if (room.partnerId || (room.memberIds || []).length >= 2) throw new Error('This room already has two players. Ask your partner to create a new room.');
    await updateDoc(roomRef, { partnerId: uid(), memberIds: [...room.memberIds, uid()] });
    state.selectedRoomId = room.id;
    selectedCoupleGameId = room.gameId;
  }
  form.reset();
  showToast('Room opened.', 'success');
  renderPage(true);
}
async function submitCoupleAnswer(answer) {
  const room = state.rooms.find(item => item.id === state.selectedRoomId);
  if (!room) throw new Error('Open a room first.');
  const members = room.memberIds || [];
  if (members.length !== 2) throw new Error('Waiting for your partner to join this room.');
  if (room.completedAt) throw new Error('This room is already complete.');
  if ((room.answeredBy || []).includes(uid())) throw new Error('You have already answered this round.');
  const answerText = String(answer || '').trim();
  if (!answerText || answerText.length > 1000) throw new Error('Choose or enter an answer first.');
  const index = Number(room.index || 0);
  const answerId = `${room.id}_${index}_${uid()}`;
  const answerRef = doc(db, 'coupleAnswers', answerId);
  const already = await getDoc(answerRef);
  if (already.exists()) throw new Error('You have already answered this round.');
  const batch = writeBatch(db);
  batch.set(answerRef, { id: answerId, userId: uid(), roomId: room.id, roundKey: String(index), memberIds: [...members], answer: answerText, expiresAt: Number(room.expiresAt || now() + 7 * 24 * 60 * 60 * 1000) });
  batch.update(doc(db, 'coupleRooms', room.id), { answeredBy: arrayUnion(uid()) });
  await batch.commit();
  coupleRoundAnswers[`${room.id}_${index}_${uid()}`] = { answer: answerText, userId: uid() };
  showToast('Answer saved. Your partner must answer before either response is revealed.', 'success');
  renderPage(true);
  const updated = state.rooms.find(item => item.id === room.id);
  if (updated && (updated.answeredBy || []).length === 2) await loadCoupleRoundAnswers(updated);
}
async function advanceCoupleRound(roomId) {
  const roomRef = doc(db, 'coupleRooms', roomId);
  await runTransaction(db, async transaction => {
    const snap = await transaction.get(roomRef);
    if (!snap.exists()) throw new Error('This room no longer exists.');
    const room = snap.data();
    const members = room.memberIds || [];
    const answeredBy = (room.answeredBy || []).filter(id => members.includes(id));
    if (members.length !== 2 || answeredBy.length < 2) throw new Error('Both players must answer before continuing.');
    const questions = coupleQuestions[room.gameId] || [];
    const nextIndex = Number(room.index || 0) + 1;
    if (nextIndex >= questions.length) transaction.update(roomRef, { completedAt: now(), answeredBy: [] });
    else transaction.update(roomRef, { index: nextIndex, answeredBy: [] });
  });
  showToast('Round updated for both players.', 'success');
  renderPage(true);
}

// Form delegation keeps the HTML shell and CSS separate from feature logic.
document.addEventListener('submit', async event => {
  const formElement = event.target;
  if (!(formElement instanceof HTMLFormElement)) return;
  const supported = new Set(['profileForm', 'chatSearchForm', 'dmMessageForm', 'createGroupForm', 'joinGroupForm', 'groupMessageForm', 'confessionForm', 'coupleCreateForm', 'coupleJoinForm', 'coupleAnswerForm', 'prefsForm']);
  if (!supported.has(formElement.id)) return;
  event.preventDefault();
  const submit = formElement.querySelector('button[type="submit"]');
  const original = submit?.textContent;
  if (submit) submit.disabled = true;
  const form = new FormData(formElement);
  try {
    if (formElement.id === 'profileForm') await saveProfile(event);
    else if (formElement.id === 'chatSearchForm') await searchChatUsername(form);
    else if (formElement.id === 'dmMessageForm') await sendDM(form);
    else if (formElement.id === 'createGroupForm') await createGroup(form);
    else if (formElement.id === 'joinGroupForm') await joinGroup(form);
    else if (formElement.id === 'groupMessageForm') await sendGroupMessage(form);
    else if (formElement.id === 'confessionForm') await createConfession(form);
    else if (formElement.id === 'coupleCreateForm') await createCoupleRoom(form);
    else if (formElement.id === 'coupleJoinForm') await joinCoupleRoom(form);
    else if (formElement.id === 'coupleAnswerForm') await submitCoupleAnswer(form.get('coupleFreeAnswer'));
    else if (formElement.id === 'prefsForm') {
      state.prefs = { showOnline: Boolean(form.get('showOnline')), showLastSeen: Boolean(form.get('showLastSeen')) };
      await setDoc(doc(db, 'userPrefs', uid()), { id: uid(), ...state.prefs }, { merge: true });
      showToast('Privacy preferences saved.', 'success');
      renderPage(false);
    }
  } catch (error) {
    console.error('[GCVERSE] Form action failed:', formElement.id, error);
    showToast(errorText(error, error.message || 'Could not complete this action.'), 'error');
  } finally {
    if (submit && document.body.contains(submit)) {
      submit.disabled = false;
      if (original && !submit.textContent.trim()) submit.textContent = original;
    }
  }
});

document.addEventListener('change', event => {
  const element = event.target;
  if (element?.id === 'confessionScope') {
    state.selectedConfessionGroupId = element.value;
    state.groupConfessions = [];
    renderPage(true);
  }
  if (element?.id === 'coupleGameId') selectedCoupleGameId = element.value;
});

document.addEventListener('click', async event => {
  const nav = event.target.closest('[data-nav]');
  if (nav) { event.preventDefault(); navigate(nav.dataset.nav); return; }
  const gameButton = event.target.closest('[data-open-game]');
  if (gameButton) {
    const gameId = gameButton.dataset.openGame;
    if (gameButton.dataset.coupleGame === 'true' || coupleGameInfo[gameId]) {
      selectedCoupleGameId = gameId;
      navigate('couples');
    } else startGame(gameId, true);
    return;
  }
  const control = event.target.closest('[data-action]');
  if (!control) return;
  const action = control.dataset.action;
  if (action === 'focus-chat-search') {
    const input = $('#chatUsernameSearch');
    if (input) { input.focus(); input.scrollIntoView({ behavior: 'smooth', block: 'center' }); }
    return;
  }
  if (action === 'focus-message') { $('#dmMessageText')?.focus(); return; }
  if (action === 'back-chat-inbox') { chatViewMode = 'inbox'; renderPage(true); return; }
  if (action === 'chat-tab') {
    const nextTab = control.dataset.tab;
    activeChatTab = ['messages', 'groups', 'requests'].includes(nextTab) ? nextTab : 'messages';
    chatViewMode = 'inbox';
    renderPage(true);
    return;
  }
  if (action === 'open-chat-channels') { activeChatTab = 'groups'; chatViewMode = 'inbox'; renderPage(true); return; }
  control.disabled = true;
  try {
    if (action === 'select-chat') { state.selectedConnectionId = control.dataset.connectionId; chatViewMode = 'conversation'; renderPage(true); }
    else if (action === 'open-chat') { state.selectedConnectionId = control.dataset.connectionId; chatViewMode = 'conversation'; renderPage(true); }
    else if (action === 'send-chat-request') { await sendChatRequest(control.dataset.userId); chatSearchResult = null; renderPage(true); }
    else if (action === 'accept-chat-request') await respondChatRequest(control.dataset.requestId, true);
    else if (action === 'reject-chat-request') await respondChatRequest(control.dataset.requestId, false);
    else if (action === 'retry-chat-request') {
      const request = state.outgoingRequests.find(item => item.id === control.dataset.requestId);
      if (request) await sendChatRequest(request.recipientId);
      renderPage(true);
    }
    else if (action === 'open-group') { state.selectedGroupId = control.dataset.groupId; state.groupMessages = []; renderPage(true); }
    else if (action === 'open-group-from-chat') { state.selectedGroupId = control.dataset.groupId; state.groupMessages = []; navigate('groups'); }
    else if (action === 'close-group') { state.selectedGroupId = ''; state.groupMessages = []; renderPage(true); }
    else if (action === 'copy-group-code' || action === 'copy-couple-code') {
      await navigator.clipboard.writeText(control.dataset.code || ''); showToast('Invite code copied.', 'success');
    }
    else if (action === 'like-confession') await likeConfession(control.dataset.postId);
    else if (action === 'report-confession') {
      if (confirm('Report this confession for review?')) await reportConfession(control.dataset.postId);
    }
    else if (action === 'delete-confession') {
      if (confirm('Delete this confession? This cannot be undone.')) await deleteConfession(control.dataset.postId);
    }
    else if (action === 'open-couple-room') { state.selectedRoomId = control.dataset.roomId; coupleRoundAnswers = {}; renderPage(true); const room = state.rooms.find(item => item.id === state.selectedRoomId); if (room) await loadCoupleRoundAnswers(room); }
    else if (action === 'close-couple-room') { state.selectedRoomId = ''; coupleRoundAnswers = {}; renderPage(true); }
    else if (action === 'couple-pick-answer') {
      const roomId = control.dataset.roomId;
      const room = state.rooms.find(item => item.id === roomId);
      const q = normalizeCoupleQuestion((coupleQuestions[room?.gameId] || [])[Number(room?.index || 0)]);
      await submitCoupleAnswer((q.options || [])[Number(control.dataset.optionIndex)]);
    }
    else if (action === 'next-couple-round') await advanceCoupleRound(control.dataset.roomId);
    else if (action === 'refresh-ranks') await loadRanks();
    else if (action === 'truth-next') {
      if (!gameRun || gameRun.id !== 'truth') return;
      const kind = control.dataset.kind;
      const pool = kind === 'dare' ? darePrompts : kind === 'truth' ? truthPrompts : [...truthPrompts, ...darePrompts];
      gameRun.prompt = pool[Math.floor(Math.random() * pool.length)];
      gameRun.answers.push(kind || 'random');
      gameRun.score += 5;
      renderPage(false);
    }
    else if (action === 'redflag-vote') {
      const run = gameRun;
      if (!run || run.id !== 'redflag' || run.finished) return;
      run.answers.push({ prompt: run.scenarios[run.index].text, vote: control.dataset.vote });
      run.score += 5;
      run.index += 1;
      if (run.index >= run.scenarios.length) run.finished = true;
      renderPage(false);
    }
    else if (action === 'complete-challenge') {
      const run = gameRun;
      if (!run || run.id !== 'challenge' || run.finished) return;
      run.answers.push(run.prompts[run.index]?.text || String(run.prompts[run.index] || ''));
      run.score += 10;
      run.index += 1;
      if (run.index >= 4 || run.index >= run.prompts.length) run.finished = true;
      renderPage(false);
    }
    else if (action === 'tmkoc-answer') {
      const run = gameRun;
      if (!run || run.id !== 'tmkoc' || run.finished) return;
      const question = tmkocQuestions[run.index];
      const option = question.options[Number(control.dataset.optionIndex)];
      run.traits[option.s] = (run.traits[option.s] || 0) + 1;
      run.answers.push(option.t);
      run.score += 10;
      run.index += 1;
      if (run.index >= tmkocQuestions.length) {
        run.finished = true;
        run.character = [...tmkocCharacters].sort((a, b) => scoreTraitFit(b, run.traits) - scoreTraitFit(a, run.traits))[0];
      }
      renderPage(false);
    }
    else if (action === 'save-tmkoc-result') await finishCurrentGame({ won: false, result: { character: gameRun?.character?.name, answers: gameRun?.answers || [] } });
    else if (action === 'puzzle-select') { if (gameRun && !gameRun.revealed) { gameRun.selected = control.dataset.answer; renderPage(false); } }
    else if (action === 'puzzle-check') {
      const run = gameRun;
      if (!run || run.id !== 'puzzle' || run.revealed) return;
      const question = run.questions[run.index];
      const correct = run.selected === question.answer;
      if (correct) run.score += 10;
      run.answers.push({ question: question.q, selected: run.selected, correct });
      run.revealed = true;
      renderPage(false);
    }
    else if (action === 'puzzle-next') {
      const run = gameRun;
      if (!run || run.id !== 'puzzle') return;
      run.index += 1; run.selected = null; run.revealed = false;
      if (run.index >= run.questions.length) renderPage(false); else renderPage(false);
      if (run.index >= run.questions.length) showToast('Puzzle set finished. Save your score to update ranks.', 'success');
    }
    else if (action === 'finish-game') {
      const run = gameRun;
      if (!run) return;
      await finishCurrentGame({ won: run.id === 'xo' && run.winner === 'X', result: { answers: run.answers || [], winner: run.winner || '' } });
    }
    else if (action === 'restart-game') startGame(gameRun?.id || activeGameId, false) || renderPage(false);
    else if (action === 'xo-move') {
      const run = gameRun;
      const index = Number(control.dataset.cellIndex);
      if (!run || run.id !== 'xo' || run.winner || run.board[index]) return;
      run.board[index] = 'X';
      run.winner = checkXO(run.board);
      if (!run.winner) {
        const open = run.board.map((cell, i) => cell ? -1 : i).filter(i => i >= 0);
        if (open.length) run.board[open[Math.floor(Math.random() * open.length)]] = 'O';
        run.winner = checkXO(run.board);
      }
      if (run.winner && !run.saved) { run.score = run.winner === 'X' ? 50 : run.winner === 'draw' ? 10 : 0; run.answers = [{ winner: run.winner, board: [...run.board] }]; }
      renderPage(false);
    }
    else if (action === 'save-xo-result') await finishCurrentGame({ won: gameRun?.winner === 'X', result: { winner: gameRun?.winner, board: gameRun?.board } });
  } catch (error) {
    console.error('[GCVERSE] Action failed:', action, error);
    showToast(errorText(error, error.message || 'Could not complete this action.'), 'error');
  } finally {
    if (document.body.contains(control)) control.disabled = false;
  }
});
function scoreTraitFit(character, traits) {
  return Object.entries(character.traits || {}).reduce((sum, [trait, value]) => sum + Number(traits[trait] || 0) * Number(value || 0), 0);
}

function closeMobileSidebar() {
  $('#sidebar').classList.remove('is-open');
  $('#sidebarBackdrop').classList.remove('is-open');
  $('#mobileMenuButton').setAttribute('aria-expanded', 'false');
}
function openMobileSidebar() {
  $('#sidebar').classList.add('is-open');
  $('#sidebarBackdrop').classList.add('is-open');
  $('#mobileMenuButton').setAttribute('aria-expanded', 'true');
}

$('#googleSignIn').addEventListener('click', beginGoogleSignIn);
$('#username').addEventListener('input', event => { event.target.value = event.target.value.toLowerCase().replace(/^@+/, '').replace(/[^a-z0-9._]/g, '').slice(0, 20); });
$('#profileSignOut').addEventListener('click', () => signOut(auth).catch(() => showToast('Could not sign out. Please try again.', 'error')));
$('#signOutButton').addEventListener('click', async () => {
  try { await signOut(auth); showToast('Signed out successfully.', 'success'); }
  catch (error) { console.error(error); showToast('Could not sign out. Please try again.', 'error'); }
});
$('#mobileMenuButton').addEventListener('click', openMobileSidebar);
$('#sidebarClose').addEventListener('click', closeMobileSidebar);
$('#sidebarBackdrop').addEventListener('click', closeMobileSidebar);
window.addEventListener('hashchange', () => {
  const page = parseHashPage();
  if (page === 'game' && gameInfo[activeGameId] && (!gameRun || gameRun.id !== activeGameId)) startGame(activeGameId, false);
  navigate(page, false);
});
window.addEventListener('keydown', event => { if (event.key === 'Escape') closeMobileSidebar(); });
getRedirectResult(auth).catch(error => {
  console.warn('[GCVERSE] Redirect result:', error?.code || error?.message || error);
  if (error) setStatus($('#authStatus'), friendlyAuthError(error), 'error');
});
onAuthStateChanged(auth, user => {
  clearPageListeners();
  if (!user) {
    currentProfile = null;
    currentStats = { xp: 0, gamesPlayed: 0, wins: 0, streak: 0, bestPuzzle: 0 };
    currentRank = null;
    activePage = 'dashboard';
    state.connections = []; state.incomingRequests = []; state.outgoingRequests = []; state.dmMessages = [];
    state.groups = []; state.groupMessages = []; state.rooms = [];
    state.confessions = []; state.groupConfessions = []; state.rankEntries = [];
    profileCache.clear(); chatSearchResult = null; gameRun = null;
    state.selectedConnectionId = ''; state.selectedGroupId = ''; state.selectedRoomId = ''; chatViewMode = 'inbox'; activeChatTab = 'messages';
    setAuthView('auth');
    setStatus($('#authStatus'), '');
    return;
  }
  void handleAuthenticatedUser(user);
});
