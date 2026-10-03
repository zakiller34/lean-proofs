# Installer Predi sur Android

| | |
|---|---|
| **Fichier** | `Predi.apk` (version 1.0.0, environ 90 Ko) |
| **Compatibilité** | Android 7.0 ou plus récent |
| **Permission demandée** | Internet uniquement (pour récupérer la météo) |

Predi n'est pas sur le Play Store. On l'installe donc directement depuis le fichier `Predi.apk`. C'est ce qu'on appelle une installation « hors Play Store » (*sideloading*).
Comptez environ 2 minutes.

---

## Étape 1 : déposer le fichier dans Google Drive

*Passez cette étape si `Predi.apk` est déjà dans votre dossier Drive « Predi ».*

1. Sur l'ordinateur, ouvrez [drive.google.com](https://drive.google.com) puis le dossier **Predi**.
2. Glissez-déposez `Predi.apk` dans la fenêtre, ou passez par **Nouveau → Importer un fichier**.

## Étape 2 : ouvrir le fichier sur le smartphone

1. Ouvrez l'application **Google Drive**, puis le dossier **Predi**.
2. Touchez **Predi.apk**.
   - Si Drive propose **Installer**, touchez-le et passez à l'étape 3.
   - Sinon, touchez **⋮ → Télécharger**. Ouvrez ensuite l'application **Fichiers** (ou **Mes fichiers** sur Samsung), allez dans **Téléchargements** et touchez **Predi.apk**.

## Étape 3 : autoriser l'installation (une seule fois)

Android affiche : *« Pour des raisons de sécurité, votre téléphone n'est pas autorisé à installer des applications inconnues provenant de cette source. »*

1. Touchez **Paramètres**.
2. Activez **Autoriser cette source** (le nom exact varie selon le téléphone : « Installer des applis inconnues », par exemple).
3. Revenez en arrière avec la flèche ou le geste retour.

## Étape 4 : installer

1. Touchez **Installer**.
2. **Google Play Protect** peut vous avertir qu'il s'agit d'une application inconnue. C'est normal pour une app installée hors Play Store.
   Touchez **Plus de détails**, puis **Installer quand même**. Si Play Protect propose d'envoyer l'application pour analyse, les deux choix fonctionnent.
3. Quand c'est terminé, touchez **Ouvrir**.

L'icône **Predi** apparaît dans la liste des applications. Faites un appui long dessus pour l'ajouter à l'écran d'accueil.

> 🔒 **Conseil :** une fois l'installation terminée, vous pouvez désactiver « Autoriser cette source » dans
> **Paramètres → Applications → Accès spécial → Installer des applis inconnues**.

---

## Utilisation

- Ouvrez l'app : la météo de **Boutonnet (Montpellier)** s'affiche, avec la situation actuelle et les prévisions **toutes les 30 minutes**.
- Le bouton **↻** en haut à droite actualise les données. L'app se met aussi à jour seule toutes les 15 minutes.
- **Sans réseau**, la dernière prévision reçue reste affichée, avec la mention « Hors ligne ». Le tout premier lancement nécessite une connexion.
- Les données viennent d'Open-Meteo (modèle AROME de Météo-France). Aucun compte n'est nécessaire et aucune donnée personnelle n'est collectée.

## Mettre à jour

Installez le nouveau fichier `Predi.apk` par-dessus l'ancien, en suivant les mêmes étapes 2 à 4.
Si Android affiche **« Application non installée »** ou un **conflit de signature**, désinstallez d'abord l'ancienne version, puis recommencez. Vous ne perdez rien : la météo est simplement rechargée.

## Désinstaller

Faites un appui long sur l'icône **Predi**, puis touchez **Désinstaller** (ou passez par **Paramètres → Applications → Predi → Désinstaller**).

## En cas de problème

| Message ou symptôme | Solution |
|---|---|
| « Erreur d'analyse du package » | Le fichier est incomplet : téléchargez-le à nouveau. Vérifiez aussi que le téléphone a Android 7.0 ou plus récent. |
| « Application non installée » | Désinstallez l'ancienne version de Predi, puis réinstallez. |
| Pas de bouton « Installer » dans Drive | Téléchargez le fichier (⋮ → Télécharger) et ouvrez-le depuis l'application Fichiers. |
| Écran « Prévision indisponible » | Vérifiez la connexion Internet, puis touchez **Réessayer**. |
| « Fin de la prévision du jour » le soir | C'est normal : la prévision couvre la journée en cours. Elle repart dès minuit. |

---

*Pour les développeurs : l'APK se reconstruit avec `npm run apk` depuis le dossier `predi/`. Il suffit d'un JDK 11 ou plus récent, sans SDK Android.*
