// Appel de l'API Open-Meteo (modèle AROME Météo-France) et normalisation du payload.
import { API, LOCATION } from '../config.js';

const TIMEOUT_MS = 10000;

/** Construit l'URL de la requête GET (virgules conservées, comme dans la spec). */
export function buildForecastUrl({ latitude, longitude } = LOCATION) {
  const params = [
    `latitude=${latitude}`,
    `longitude=${longitude.toFixed(3)}`,
    `hourly=${API.hourly.join(',')}`,
    `minutely_15=${API.minutely15.join(',')}`,
    `timezone=${encodeURIComponent(API.timezone)}`,
    `forecast_days=${API.forecastDays}`,
  ];
  return `${API.baseUrl}?${params.join('&')}`;
}

const toNumber = (v) => (typeof v === 'number' && Number.isFinite(v) ? v : null);

/**
 * Transforme la réponse brute en une liste de créneaux de 15 min.
 * Les heures sont des chaînes locales Europe/Paris ("YYYY-MM-DDTHH:mm").
 */
export function parseForecast(payload) {
  const m = payload?.minutely_15;
  if (!m || !Array.isArray(m.time) || m.time.length === 0) {
    throw new Error('Réponse API invalide : données 15 min absentes');
  }

  // Probabilité de précipitation horaire, indexée par "YYYY-MM-DDTHH".
  const probaByHour = new Map();
  const h = payload.hourly;
  if (h && Array.isArray(h.time)) {
    h.time.forEach((t, i) => {
      probaByHour.set(t.slice(0, 13), toNumber(h.precipitation_probability?.[i]));
    });
  }

  const codes = m.weathercode ?? m.weather_code ?? [];
  const slots = m.time.map((time, i) => ({
    time,
    temperature: toNumber(m.temperature_2m?.[i]),
    humidity: toNumber(m.relative_humidity_2m?.[i]),
    windSpeed: toNumber(m.wind_speed_10m?.[i]),
    precipitation: toNumber(m.precipitation?.[i]),
    weatherCode: toNumber(codes[i]),
    precipitationProbability: probaByHour.get(time.slice(0, 13)) ?? null,
  }));

  return {
    utcOffsetSeconds: toNumber(payload.utc_offset_seconds) ?? 0,
    slots,
  };
}

/** Récupère et normalise la prévision. `fetchImpl` est injectable pour les tests. */
export async function fetchForecast({ fetchImpl = globalThis.fetch, url = buildForecastUrl() } = {}) {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), TIMEOUT_MS);
  try {
    const res = await fetchImpl(url, { signal: controller.signal });
    const body = await res.json().catch(() => null);
    if (!res.ok || body?.error) {
      throw new Error(body?.reason || `Erreur API (HTTP ${res.status})`);
    }
    return parseForecast(body);
  } catch (err) {
    if (err?.name === 'AbortError') throw new Error('Délai de réponse dépassé');
    throw err;
  } finally {
    clearTimeout(timer);
  }
}
