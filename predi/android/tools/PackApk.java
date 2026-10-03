import com.android.apksig.ApkSigner;
import com.android.apksig.ApkVerifier;
import com.reandroid.apk.ApkModule;
import com.reandroid.apk.ApkModuleXmlEncoder;

import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.security.KeyStore;
import java.security.PrivateKey;
import java.security.cert.X509Certificate;
import java.util.Collections;

/**
 * Assemble et signe l'APK Predi sans le SDK Android :
 *  1. ARSCLib encode le manifest et les ressources (XML -> binaire) et empaquette le dossier ;
 *  2. apksig aligne et signe (schéma v2, suffisant dès Android 7.0).
 *
 * Usage : java PackApk <dossier-module> <keystore.p12> <mot-de-passe> <alias> <sortie.apk>
 */
public class PackApk {
    public static void main(String[] args) throws Exception {
        File moduleDir = new File(args[0]);
        File keystore = new File(args[1]);
        char[] password = args[2].toCharArray();
        String alias = args[3];
        File output = new File(args[4]);
        File unsigned = new File(output.getPath() + ".unsigned");

        ApkModuleXmlEncoder encoder = new ApkModuleXmlEncoder();
        encoder.scanDirectory(moduleDir);
        ApkModule module = encoder.getApkModule();
        module.writeApk(unsigned);

        KeyStore ks = KeyStore.getInstance("PKCS12");
        try (InputStream in = new FileInputStream(keystore)) {
            ks.load(in, password);
        }
        PrivateKey key = (PrivateKey) ks.getKey(alias, password);
        X509Certificate cert = (X509Certificate) ks.getCertificate(alias);

        ApkSigner.SignerConfig signer =
                new ApkSigner.SignerConfig.Builder("PREDI", key, Collections.singletonList(cert)).build();
        new ApkSigner.Builder(Collections.singletonList(signer))
                .setInputApk(unsigned)
                .setOutputApk(output)
                .setMinSdkVersion(24)
                .setV1SigningEnabled(false) // v2 suffit : minSdk 24 (Android 7.0)
                .setV2SigningEnabled(true)
                .build()
                .sign();
        unsigned.delete();

        ApkVerifier.Result result = new ApkVerifier.Builder(output).build().verify();
        if (!result.isVerified()) {
            System.err.println("Signature invalide : " + result.getErrors());
            System.exit(1);
        }
        System.out.println("APK signé (v1=" + result.isVerifiedUsingV1Scheme()
                + ", v2=" + result.isVerifiedUsingV2Scheme() + ") : " + output);
    }
}
