# Predi

Une PWA minimaliste de prévision météo à très court terme pour le **quartier Boutonnet, à Montpellier** (43.627, 3.860).
Les données viennent de [Open-Meteo](https://open-meteo.com/), modèle **AROME Météo-France** : API gratuite, sans clé.

- **Mobile (Android, moins de 768 px)** : une colonne, prévision au **pas de 30 min** sur 12 créneaux (6 h).
- **Desktop (Windows, 768 px et plus)** : deux colonnes, prévision au **pas de 15 min** sur 24 créneaux (6 h).
- **Dark mode** par défaut (manifest, `theme-color`, CSS). La palette claire suit `prefers-color-scheme: light`.
- **Installable** grâce au manifest et au Service Worker. La coquille reste disponible hors ligne, et la dernière prévision est gardée en local.
- Les codes **WMO** correspondent à des icônes **SVG** inline, avec une variante nuit selon la position du soleil, calculée en local.

## Lancer

```bash
cd predi
npm start        # http://localhost:8080 (serveur statique sans dépendance)
npm test         # tests unitaires (node:test, Node ≥ 18)
npm run icons    # régénère les PNG à partir de icons/icon.svg (nécessite playwright)
```

Il n'y a ni build ni dépendance npm. Pour la production, servez le dossier `predi/` tel quel en **HTTPS** : GitHub Pages, Netlify, etc.
Tous les chemins sont relatifs, donc l'app fonctionne aussi dans un sous-dossier.

### Installer l'app

- **Android (Chrome)** : menu ⋮, puis « Installer l'application ».
- **Windows (Edge/Chrome)** : icône d'installation dans la barre d'adresse.

## Arborescence

```text
predi/
  index.html, manifest.json, sw.js   -> coquille PWA (le SW est à la racine pour couvrir tout le scope)
  icons/                             -> icône SVG + PNG 192/512/maskable
  src/
    config.js                        -> localisation, paramètres API, pas d'affichage
    main.js                          -> état minimal, rendu, rafraîchissement, enregistrement du SW
    api/openMeteo.js                 -> URL de requête, appel fetch, normalisation du payload
    components/                      -> CurrentWeather, ForecastList, WeatherIcon (fonctions qui renvoient du HTML)
    utils/                           -> wmo (codes → libellé/icône), time, sun (jour/nuit), format
    styles/main.css                  -> variables, mobile-first, responsive desktop, dark mode
  tests/                             -> tests unitaires node:test
  scripts/                           -> serveur de dev, génération des icônes
```

## Choix techniques

- **Requête API** : exactement celle de la spécification (`forecast_days=1`). Conséquence : en fin de soirée, il reste
  peu de créneaux à afficher, puis le message « Fin de la prévision du jour » apparaît. Pour avoir plus de profondeur, passez
  `API.forecastDays` à `2` dans `src/config.js`.
- **Heure courante** : elle est toujours calculée en heure de Paris (`Intl`), quel que soit le fuseau de l'appareil, pour correspondre
  aux heures locales renvoyées par l'API.
- **Pas de 30 min** : les précipitations des deux quarts d'heure sont cumulées, et c'est le code météo le plus sévère qui est retenu.
- **Codes météo absents** : si l'API ne renvoie pas de `weathercode`, un code « pluie » est déduit des précipitations.
- **Rafraîchissement** : toutes les 15 min quand l'onglet est visible, au retour au premier plan et au retour du réseau.
  Le créneau « maintenant » avance chaque minute, sans appel réseau.
- **Mise à jour de l'app** : incrémentez `VERSION` dans `sw.js` à chaque déploiement.
