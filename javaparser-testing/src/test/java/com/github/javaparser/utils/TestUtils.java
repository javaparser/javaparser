package com.github.javaparser.utils;

import com.github.javaparser.*;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.validator.Java9Validator;
import okhttp3.OkHttpClient;
import okhttp3.Request;
import okhttp3.Response;

import java.io.*;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.Utils.EOL;
import static com.github.javaparser.utils.Utils.normalizeEolInTextBlock;
import static java.util.Arrays.*;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;

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

    public static void assertInstanceOf(Class<?> expectedType, Object instance) {
        assertEquals(true, expectedType.isAssignableFrom(instance.getClass()), f("%s is not an instance of %s.", instance.getClass(), expectedType));
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

    public static void assertCollections(Collection<?> expected, Collection<?> actual) {
        final StringBuilder out = new StringBuilder();
        for (Object e : expected) {
            if (actual.contains(e)) {
                actual.remove(e);
            } else {
                out.append("Missing: ").append(e).append(EOL);
            }
        }
        for (Object a : actual) {
            out.append("Unexpected: ").append(a).append(EOL);
        }

        String s = out.toString();
        if (s.isEmpty()) {
            return;
        }
        fail(s);
    }

    public static void assertProblems(ParseResult<?> result, String... expectedArg) {
        assertProblems(result.getProblems(), expectedArg);
    }

    public static void assertProblems(List<Problem> result, String... expectedArg) {
        Set<String> actual = result.stream().map(Problem::toString).collect(Collectors.toSet());
        Set<String> expected = new HashSet<>(asList(expectedArg));
        assertCollections(expected, actual);
    }

    public static void assertNoProblems(ParseResult<?> result) {
        assertProblems(result);
    }

    public static void assertExpressionValid(String expression) {
        JavaParser javaParser = new JavaParser(new ParserConfiguration().setValidator(new Java9Validator()));
        ParseResult<Expression> result = javaParser.parse(ParseStart.EXPRESSION, provider(expression));
        assertEquals(true, result.isSuccessful(), result.getProblems().toString());
    }

    /**
     * Assert that "actual" equals "expected", and that any EOL characters in "actual" are correct for the platform.
     */
    public static void assertEqualsNoEol(String expected, String actual) {
        assertEquals(normalizeEolInTextBlock(expected, EOL), actual);
    }
}
