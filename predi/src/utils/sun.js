// Jour / nuit par élévation solaire (formule astronomique simplifiée, précision ~1°).
// Évite un appel API supplémentaire pour afficher soleil ou lune.

const RAD = Math.PI / 180;

/** Élévation du soleil (degrés) pour une date UTC et une position. */
export function solarElevation(date, latitude, longitude) {
  const d = date.getTime() / 86400000 - 10957.5; // jours depuis J2000.0
  const g = (357.529 + 0.98560028 * d) * RAD; // anomalie moyenne
  const q = 280.459 + 0.98564736 * d; // longitude moyenne
  const lambda = (q + 1.915 * Math.sin(g) + 0.02 * Math.sin(2 * g)) * RAD;
  const eps = (23.439 - 0.00000036 * d) * RAD;
  const decl = Math.asin(Math.sin(eps) * Math.sin(lambda));
  const ra = Math.atan2(Math.cos(eps) * Math.sin(lambda), Math.cos(lambda));
  const gmst = (18.697374558 + 24.06570982441908 * d) % 24; // heures
  const hourAngle = (gmst * 15 + longitude) * RAD - ra;
  const lat = latitude * RAD;
  return (
    Math.asin(
      Math.sin(lat) * Math.sin(decl) + Math.cos(lat) * Math.cos(decl) * Math.cos(hourAngle),
    ) / RAD
  );
}

/** Convertit une heure locale API ("YYYY-MM-DDTHH:mm") en Date UTC grâce au décalage renvoyé par l'API. */
export function localTimeToDate(time, utcOffsetSeconds) {
  const [date, clock] = time.split('T');
  const [y, mo, da] = date.split('-').map(Number);
  const [h, mi] = clock.split(':').map(Number);
  return new Date(Date.UTC(y, mo - 1, da, h, mi) - utcOffsetSeconds * 1000);
}

/** Vrai si le soleil est au-dessus de l'horizon (réfraction incluse : -0,833°). */
export function isDaytime(time, utcOffsetSeconds, latitude, longitude) {
  return solarElevation(localTimeToDate(time, utcOffsetSeconds), latitude, longitude) > -0.833;
}
