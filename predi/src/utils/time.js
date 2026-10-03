// Helpers de dates : heure locale Europe/Paris, sélection et agrégation des créneaux.

const pad = (n) => String(n).padStart(2, '0');

/** Heure courante à Paris au format API "YYYY-MM-DDTHH:mm", quel que soit le fuseau de l'appareil. */
export function nowInParis(date = new Date(), timeZone = 'Europe/Paris') {
  const parts = Object.fromEntries(
    new Intl.DateTimeFormat('en-GB', {
      timeZone,
      year: 'numeric',
      month: '2-digit',
      day: '2-digit',
      hour: '2-digit',
      minute: '2-digit',
      hourCycle: 'h23',
    })
      .formatToParts(date)
      .map((p) => [p.type, p.value]),
  );
  return `${parts.year}-${parts.month}-${parts.day}T${parts.hour}:${parts.minute}`;
}

/** "2026-10-03T14:30" -> "14h30" */
export function formatSlotTime(time) {
  const [hh, mm] = time.slice(11, 16).split(':');
  return `${Number(hh)}h${mm}`;
}

/** Date JS -> "14:05" (heure de l'appareil, pour "mis à jour à"). */
export function formatClock(date) {
  return `${pad(date.getHours())}:${pad(date.getMinutes())}`;
}

/** Index du créneau en cours (dernier créneau dont l'heure est <= maintenant). */
export function currentSlotIndex(slots, now) {
  let idx = -1;
  for (let i = 0; i < slots.length; i++) {
    if (slots[i].time <= now) idx = i;
    else break;
  }
  return idx;
}

const maxOrNull = (a, b) => (a === null ? b : b === null ? a : Math.max(a, b));
const sumOrNull = (a, b) => (a === null && b === null ? null : (a ?? 0) + (b ?? 0));

/**
 * Créneaux futurs (après `now`) au pas demandé (15 ou 30 min).
 * Au pas de 30 min, les précipitations des deux quarts d'heure sont cumulées
 * et le code météo le plus sévère est retenu.
 */
export function forecastSlots(slots, now, step, limit) {
  const out = [];
  for (let i = 0; i < slots.length && out.length < limit; i++) {
    const s = slots[i];
    if (s.time <= now) continue;
    if (step === 30) {
      if (Number(s.time.slice(14, 16)) % 30 !== 0) continue;
      const prev = slots[i - 1];
      if (prev) {
        out.push({
          ...s,
          precipitation: sumOrNull(prev.precipitation, s.precipitation),
          weatherCode: maxOrNull(prev.weatherCode, s.weatherCode),
        });
        continue;
      }
    }
    out.push(s);
  }
  return out;
}
