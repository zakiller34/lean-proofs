// Formatage des valeurs météo pour l'affichage (locale fr-FR).

const DASH = '–';
const oneDecimal = new Intl.NumberFormat('fr-FR', { minimumFractionDigits: 1, maximumFractionDigits: 1 });

export const formatTemp = (v) => (v === null ? DASH : `${Math.round(v)}°`);
export const formatHumidity = (v) => (v === null ? DASH : `${Math.round(v)} %`);
export const formatWind = (v) => (v === null ? DASH : `${Math.round(v)} km/h`);
export const formatPrecip = (v) => (v === null ? DASH : `${oneDecimal.format(v)} mm`);
export const formatProba = (v) => (v === null ? DASH : `${Math.round(v)} %`);

/** Pluie significative (seuil de mesure : 0,1 mm). */
export const isWet = (mm) => mm !== null && mm >= 0.1;
