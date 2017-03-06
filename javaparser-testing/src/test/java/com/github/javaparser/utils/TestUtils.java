package com.github.javaparser.utils;

import okhttp3.OkHttpClient;
import okhttp3.Request;
import okhttp3.Response;

import java.io.*;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class TestUtils {
    /**
     * Takes care of setting all the end of line character to platform specific ones.
     */
    public static String readResource(String resourceName) throws IOException {
        if (resourceName.startsWith("/")) {
            resourceName = resourceName.substring(1);
        }
        try (final InputStream resourceAsStream = TestUtils.class.getClassLoader().getResourceAsStream(resourceName)) {
            if (resourceAsStream == null) {
                fail("not found: " + resourceName);
            }
            try (final InputStreamReader reader = new InputStreamReader(resourceAsStream, "utf-8");
                 final BufferedReader br = new BufferedReader(reader)) {
                final StringBuilder builder = new StringBuilder();
                String line;
                while ((line = br.readLine()) != null) {
                    builder.append(line).append(Utils.EOL);
                }
                return builder.toString();
            }
        }
    }

    public static void assertInstanceOf(Class<? extends Throwable> expectedType, Throwable instance) {
        assertTrue(expectedType.isAssignableFrom(instance.getClass()));
    }

    /**
     * Unzip a zip file into a directory.
     */
    public static void unzip(Path zipFile, Path outputFolder) throws IOException {
        Log.info("Unzipping %s to %s", zipFile, outputFolder);

        final byte[] buffer = new byte[1024 * 1024];

        outputFolder.toFile().mkdirs();

        try (ZipInputStream zis = new ZipInputStream(new FileInputStream(zipFile.toFile()))) {
            ZipEntry ze = zis.getNextEntry();

            while (ze != null) {
                final Path newFile = outputFolder.resolve(ze.getName());

                if (ze.isDirectory()) {
                    Log.trace("mkdir %s", newFile.toAbsolutePath());
                    newFile.toFile().mkdirs();
                } else {
                    Log.info("unzip %s", newFile.toAbsolutePath());
                    try (FileOutputStream fos = new FileOutputStream(newFile.toFile())) {
                        int len;
                        while ((len = zis.read(buffer)) > 0) {
                            fos.write(buffer, 0, len);
                        }
                    }
                }
                zis.closeEntry();
                ze = zis.getNextEntry();
            }

        }
        Log.info("Unzipped %s to %s", zipFile, outputFolder);
    }

    /**
     * Download a file from a URL to disk.
     */
    public static void download(URL url, Path destination) throws IOException {
        OkHttpClient client = new OkHttpClient();
        Request request = new Request.Builder()
                .url(url)
                .build();

        Response response = client.newCall(request).execute();
        Files.write(destination, response.body().bytes());
    }

    public static String temporaryDirectory() {
        return System.getProperty("java.io.tmpdir");
    }
}
