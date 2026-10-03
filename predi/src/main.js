// Point d'entrée : état minimal, chargement des données, rendu et enregistrement du Service Worker.
import { DESKTOP_QUERY, FORECAST_SLOTS, LOCATION, REFRESH_MS, STEP_DESKTOP, STEP_MOBILE } from './config.js';
import { fetchForecast } from './api/openMeteo.js';
import { currentSlotIndex, forecastSlots, formatClock, nowInParis } from './utils/time.js';
import { describeWeather } from './utils/wmo.js';
import { isDaytime } from './utils/sun.js';
import { CurrentWeather } from './components/CurrentWeather.js';
import { ForecastList } from './components/ForecastList.js';

const CACHE_KEY = 'predi:last-forecast';

const app = document.getElementById('app');
const statusEl = document.getElementById('status');
const refreshBtn = document.getElementById('refresh');
const desktop = matchMedia(DESKTOP_QUERY);

const state = { forecast: null, updatedAt: null, error: null, loading: false };

// --- Persistance de la dernière prévision (mode hors ligne) ---------------------------
function loadCached() {
  try {
    const raw = localStorage.getItem(CACHE_KEY);
    if (!raw) return;
    const { forecast, updatedAt } = JSON.parse(raw);
    state.forecast = forecast;
    state.updatedAt = new Date(updatedAt);
  } catch {
    /* stockage indisponible : on continue sans cache */
  }
}

function saveCached() {
  try {
    localStorage.setItem(CACHE_KEY, JSON.stringify({ forecast: state.forecast, updatedAt: state.updatedAt }));
  } catch {
    /* quota ou navigation privée : sans conséquence */
  }
}

// --- Rendu -----------------------------------------------------------------------------
const withWeather = (slot, offset) => ({
  ...slot,
  weather: describeWeather(slot.weatherCode, {
    precipitation: slot.precipitation,
    isDay: isDaytime(slot.time, offset, LOCATION.latitude, LOCATION.longitude),
  }),
});

function renderStatus() {
  refreshBtn.disabled = state.loading;
  refreshBtn.classList.toggle('is-loading', state.loading);
  if (state.loading) statusEl.textContent = 'Mise à jour…';
  else if (!state.updatedAt) statusEl.textContent = '';
  else if (state.error) statusEl.textContent = `Hors ligne · données de ${formatClock(state.updatedAt)}`;
  else statusEl.textContent = `Mis à jour à ${formatClock(state.updatedAt)}`;
  statusEl.classList.toggle('is-error', Boolean(state.error));
}

const escapeHtml = (s) =>
  String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);

function renderMessage(title, text, withRetry) {
  app.innerHTML = `
    <div class="message">
      <p class="message__title">${title}</p>
      <p>${escapeHtml(text)}</p>
      ${withRetry ? '<button class="button" type="button" data-action="retry">Réessayer</button>' : ''}
    </div>`;
}

function render() {
  renderStatus();
  const { forecast } = state;
  if (!forecast) {
    if (state.error) renderMessage('Prévision indisponible', state.error, true);
    else if (state.loading) app.innerHTML = '<div class="skeleton" aria-hidden="true"></div>';
    return;
  }

  const now = nowInParis();
  const { slots, utcOffsetSeconds } = forecast;
  if (now.slice(0, 10) > slots[slots.length - 1].time.slice(0, 10)) {
    renderMessage('Données expirées', 'La dernière prévision enregistrée date d’un jour précédent.', true);
    return;
  }

  const step = desktop.matches ? STEP_DESKTOP : STEP_MOBILE;
  const current = slots[Math.max(0, currentSlotIndex(slots, now))];
  const next = forecastSlots(slots, now, step, FORECAST_SLOTS[step]);

  app.innerHTML =
    CurrentWeather(withWeather(current, utcOffsetSeconds)) +
    ForecastList(next.map((s) => withWeather(s, utcOffsetSeconds)), step);
}

// --- Données ---------------------------------------------------------------------------
async function refresh() {
  if (state.loading) return;
  state.loading = true;
  render();
  try {
    state.forecast = await fetchForecast();
    state.updatedAt = new Date();
    state.error = null;
    saveCached();
  } catch (err) {
    state.error = navigator.onLine === false ? 'Pas de connexion réseau.' : err.message;
  } finally {
    state.loading = false;
    render();
  }
}

// --- Démarrage -------------------------------------------------------------------------
loadCached();
render();
refresh();

refreshBtn.addEventListener('click', refresh);
app.addEventListener('click', (e) => {
  if (e.target.closest('[data-action="retry"]')) refresh();
});
desktop.addEventListener('change', render);
window.addEventListener('online', refresh);
document.addEventListener('visibilitychange', () => {
  if (document.visibilityState !== 'visible') return;
  const age = state.updatedAt ? Date.now() - state.updatedAt.getTime() : Infinity;
  if (age > REFRESH_MS) refresh();
  else render(); // met à jour le créneau « maintenant »
});
setInterval(() => (document.visibilityState === 'visible' ? refresh() : null), REFRESH_MS);
setInterval(render, 60 * 1000); // fait avancer « maintenant » sans appel réseau

if ('serviceWorker' in navigator) {
  window.addEventListener('load', () => {
    navigator.serviceWorker.register('./sw.js').catch((err) => console.warn('Service Worker :', err));
  });
}
