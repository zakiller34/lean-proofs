// Bloc « maintenant » : grande icône, température et détails du créneau en cours.
import { WeatherIcon } from './WeatherIcon.js';
import { formatSlotTime } from '../utils/time.js';
import { formatHumidity, formatPrecip, formatProba, formatTemp, formatWind } from '../utils/format.js';

const detail = (name, value) => `<div class="detail"><dt>${name}</dt><dd>${value}</dd></div>`;

/** `slot` est un créneau enrichi d'un champ `weather` ({ label, icon }). */
export function CurrentWeather(slot) {
  const { weather } = slot;
  const proba =
    slot.precipitationProbability === null ? '' : detail('Risque de pluie', formatProba(slot.precipitationProbability));
  return `
    <section class="current" aria-labelledby="current-title">
      <h2 id="current-title" class="visually-hidden">Maintenant</h2>
      <p class="current__time">Maintenant · ${formatSlotTime(slot.time)}</p>
      <div class="current__main">
        ${WeatherIcon(weather.icon, { size: 96, label: weather.label })}
        <p class="current__temp">${formatTemp(slot.temperature)}</p>
      </div>
      <p class="current__label">${weather.label}</p>
      <dl class="current__details">
        ${detail('Humidité', formatHumidity(slot.humidity))}
        ${detail('Vent', formatWind(slot.windSpeed))}
        ${detail('Pluie (15 min)', formatPrecip(slot.precipitation))}
        ${proba}
      </dl>
    </section>`;
}
