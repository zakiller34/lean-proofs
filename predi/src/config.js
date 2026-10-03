// Configuration centrale de Predi (localisation fixe, API, pas d'affichage).

export const LOCATION = Object.freeze({
  name: 'Boutonnet',
  city: 'Montpellier',
  latitude: 43.627,
  longitude: 3.86,
});

export const API = Object.freeze({
  baseUrl: 'https://api.open-meteo.com/v1/meteofrance',
  timezone: 'Europe/Paris',
  forecastDays: 1,
  hourly: ['precipitation_probability'],
  minutely15: [
    'temperature_2m',
    'relative_humidity_2m',
    'wind_speed_10m',
    'precipitation',
    'weathercode',
  ],
});

// Pas de prévision (minutes) : 30 min sur mobile (Android), 15 min sur desktop (Windows).
export const STEP_MOBILE = 30;
export const STEP_DESKTOP = 15;
export const DESKTOP_QUERY = '(min-width: 768px)';

// Nombre de créneaux affichés dans la liste de prévision.
export const FORECAST_SLOTS = { 30: 12, 15: 24 };

// Rafraîchissement automatique des données.
export const REFRESH_MS = 15 * 60 * 1000;
