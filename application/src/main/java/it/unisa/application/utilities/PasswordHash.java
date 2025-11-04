package it.unisa.application.utilities;

import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

public class PasswordHash {

    public static String hash(String password) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-1");
            digest.reset();
            digest.update(password.getBytes(StandardCharsets.UTF_8));
            String hash = String.format("%040x", new BigInteger(1, digest.digest()));
            StringBuilder hexString = new StringBuilder();
            for (int i = 0; i < hash.length(); i++) {
                hexString.append(hash.charAt(i));
            }
            return hexString.toString();
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
    }
}
