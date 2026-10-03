#!/usr/bin/env bash
# Construit dist/Predi.apk : la PWA Predi embarquée dans une WebView Android.
# Pas de SDK Android requis : uniquement un JDK (11+) et des outils récupérés sur Maven Central.
#
# Variables optionnelles :
#   PREDI_KEYSTORE   keystore PKCS12 de signature (créé s'il n'existe pas)
#   PREDI_STOREPASS  mot de passe du keystore (défaut : predi-android)
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
PREDI="$(dirname "$HERE")"
TOOLS="$HERE/.tools"
BUILD="$HERE/build"
OUT="$PREDI/dist/Predi.apk"
KEYSTORE="${PREDI_KEYSTORE:-$HERE/predi-release.p12}"
STOREPASS="${PREDI_STOREPASS:-predi-android}"
ALIAS=predi
MAVEN=https://repo1.maven.org/maven2

fetch() { # <chemin maven> <fichier local>
  [ -s "$TOOLS/$2" ] || curl -sSfL --retry 3 -o "$TOOLS/$2" "$MAVEN/$1"
}

echo "▸ Outils (Maven Central)"
mkdir -p "$TOOLS"
fetch com/google/android/android/4.1.1.4/android-4.1.1.4.jar android.jar            # API Android (compilation)
fetch com/jakewharton/android/repackaged/dalvik-dx/16.0.1/dalvik-dx-16.0.1.jar dx.jar # .class -> .dex
fetch io/github/reandroid/ARSCLib/1.4.0/ARSCLib-1.4.0.jar arsclib.jar                # manifest/ressources binaires
fetch com/android/tools/build/apksig/2.3.0/apksig-2.3.0.jar apksig.jar              # signature APK v1+v2

rm -rf "$BUILD"
MODULE="$BUILD/module"
mkdir -p "$BUILD/classes" "$BUILD/tools" "$MODULE/root/assets/www" "$MODULE/resources/package_1"

echo "▸ Compilation Java"
javac -nowarn --release 8 -cp "$TOOLS/android.jar" \
  -d "$BUILD/classes" $(find "$HERE/src" -name '*.java')
java -cp "$TOOLS/dx.jar" com.android.dx.command.Main --dex --min-sdk-version=24 \
  --output="$MODULE/root/classes.dex" "$BUILD/classes"

echo "▸ Ressources et PWA embarquée"
cp "$HERE/AndroidManifest.xml" "$MODULE/"
cp -R "$HERE/res" "$MODULE/resources/package_1/res"
printf '{"package_id": 127, "package_name": "fr.predi.app"}\n' > "$MODULE/resources/package_1/package.json"
cp -R "$PREDI/index.html" "$PREDI/manifest.json" "$PREDI/sw.js" "$PREDI/icons" "$PREDI/src" "$MODULE/root/assets/www/"

if [ ! -f "$KEYSTORE" ]; then
  echo "▸ Création du keystore de signature : $KEYSTORE"
  keytool -genkeypair -keystore "$KEYSTORE" -storetype PKCS12 -storepass "$STOREPASS" \
    -alias "$ALIAS" -keyalg RSA -keysize 2048 -validity 10000 -dname "CN=Predi, O=Predi, C=FR" 2>/dev/null
fi

echo "▸ Assemblage et signature"
CP="$TOOLS/arsclib.jar:$TOOLS/apksig.jar"
javac -nowarn -cp "$CP" -d "$BUILD/tools" "$HERE/tools/PackApk.java"
mkdir -p "$(dirname "$OUT")"
java --add-exports java.base/sun.security.x509=ALL-UNNAMED --add-exports java.base/sun.security.pkcs=ALL-UNNAMED \
  --add-exports java.base/sun.security.util=ALL-UNNAMED -cp "$CP:$BUILD/tools" PackApk "$MODULE" "$KEYSTORE" "$STOREPASS" "$ALIAS" "$OUT"
echo "✔ $(du -h "$OUT" | cut -f1)  $OUT"
