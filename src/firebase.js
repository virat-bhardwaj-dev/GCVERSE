import { initializeApp } from 'https://www.gstatic.com/firebasejs/11.10.0/firebase-app.js';
import { getAuth, GoogleAuthProvider } from 'https://www.gstatic.com/firebasejs/11.10.0/firebase-auth.js';
import { getFirestore } from 'https://www.gstatic.com/firebasejs/11.10.0/firebase-firestore.js';

// Firebase web configuration is client-side configuration, not a server secret.
// Protect data and privileged operations with Firebase Authentication and Firestore Rules.
const firebaseConfig = {
  apiKey: 'AIzaSyB5n2L0mKUKxcwlUYa_BW_tR-x98G2zxbY',
  authDomain: 'gcverse-3b48c.firebaseapp.com',
  projectId: 'gcverse-3b48c',
  storageBucket: 'gcverse-3b48c.firebasestorage.app',
  messagingSenderId: '214074252875',
  appId: '1:214074252875:web:fbcc066a4155b99e3cb7ce',
  measurementId: 'G-ZZ2P462BXN'
};

export const firebaseApp = initializeApp(firebaseConfig);
export const auth = getAuth(firebaseApp);
export const db = getFirestore(firebaseApp);
export const googleProvider = new GoogleAuthProvider();
googleProvider.setCustomParameters({ prompt: 'select_account' });
