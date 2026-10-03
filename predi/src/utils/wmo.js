// Mapping des codes météo WMO vers un libellé français et une icône SVG.

const WMO = {
  0: ['Ciel dégagé', 'clear'],
  1: ['Plutôt dégagé', 'clear'],
  2: ['Partiellement nuageux', 'partly'],
  3: ['Couvert', 'cloudy'],
  45: ['Brouillard', 'fog'],
  48: ['Brouillard givrant', 'fog'],
  51: ['Bruine légère', 'drizzle'],
  53: ['Bruine', 'drizzle'],
  55: ['Bruine dense', 'drizzle'],
  56: ['Bruine verglaçante', 'sleet'],
  57: ['Bruine verglaçante dense', 'sleet'],
  61: ['Pluie faible', 'rain'],
  63: ['Pluie modérée', 'rain'],
  65: ['Pluie forte', 'heavy-rain'],
  66: ['Pluie verglaçante', 'sleet'],
  67: ['Pluie verglaçante forte', 'sleet'],
  71: ['Neige faible', 'snow'],
  73: ['Neige modérée', 'snow'],
  75: ['Neige forte', 'snow'],
  77: ['Grains de neige', 'snow'],
  80: ['Averses faibles', 'showers'],
  81: ['Averses', 'showers'],
  82: ['Averses violentes', 'heavy-rain'],
  85: ['Averses de neige', 'snow'],
  86: ['Fortes averses de neige', 'snow'],
  95: ['Orage', 'thunder'],
  96: ['Orage avec grêle', 'thunder'],
  99: ['Orage avec forte grêle', 'thunder'],
};

// Icônes qui ont une variante nuit (soleil -> lune).
const HAS_NIGHT_VARIANT = new Set(['clear', 'partly']);

/**
 * Déduit un code WMO des précipitations (mm / 15 min) si l'API n'en fournit pas.
 * Seuils approximatifs : < 0,1 mm sec ; < 0,6 faible ; < 2 modérée ; au-delà forte.
 */
export function codeFromPrecipitation(mm) {
  if (mm === null || mm < 0.1) return null;
  if (mm < 0.6) return 61;
  if (mm < 2) return 63;
  return 65;
}

/** Retourne { label, icon } pour un créneau. `isDay` sélectionne soleil ou lune. */
export function describeWeather(code, { isDay = true, precipitation = null } = {}) {
  const effective = code ?? codeFromPrecipitation(precipitation);
  const entry = WMO[effective];
  if (!entry) return { label: 'Indisponible', icon: 'unknown' };
  const [label, icon] = entry;
  return { label, icon: !isDay && HAS_NIGHT_VARIANT.has(icon) ? `${icon}-night` : icon };
}
