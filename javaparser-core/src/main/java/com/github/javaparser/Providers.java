package com.github.javaparser;

import java.io.*;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Factory for providers of source code for JavaParser.
 * Providers that have no parameter for encoding but need it will use UTF-8.
 */
public final class Providers {
    public static final Charset UTF8 = Charset.forName("utf-8");

    private Providers() {
    }

    public static Provider provider(Reader reader) {
        return new StreamProvider(assertNotNull(reader));
    }

    public static Provider provider(InputStream input, Charset encoding) {
        assertNotNull(input);
        assertNotNull(encoding);
        try {
            return new StreamProvider(input, encoding.name());
        } catch (IOException e) {
            // The only one that is thrown is UnsupportedCharacterEncodingException,
            // and that's a fundamental problem, so runtime exception.
            throw new RuntimeException(e);
        }
    }

    public static Provider provider(InputStream input) {
        return provider(input, UTF8);
    }

    public static Provider provider(File file, Charset encoding) throws FileNotFoundException {
        return provider(new FileInputStream(assertNotNull(file)), assertNotNull(encoding));
    }

    public static Provider provider(File file) throws FileNotFoundException {
        return provider(assertNotNull(file), UTF8);
    }

    public static Provider provider(Path path, Charset encoding) throws IOException {
        return provider(Files.newInputStream(assertNotNull(path)), assertNotNull(encoding));
    }

    public static Provider provider(Path path) throws IOException {
        return provider(assertNotNull(path), UTF8);
    }

    public static Provider provider(String source) {
        return new StringProvider(assertNotNull(source));
    }



    /**
     * Provide a Provider from the resource found in classLoader
     * @param classLoader Class loader in which resource is searched
     * @param pathToResource path to resource in provided class loader. As working relatively to a class loader, no "/"
     * at the beginning of the path
     * @param encoding encoding
     * @return the provider associated to pathToResource
     */
    public static Provider resourceProvider(ClassLoader classLoader, String pathToResource, Charset encoding) {
        return provider(classLoader.getResourceAsStream(pathToResource), encoding);
    }

    public static Provider resourceProvider(String pathToResource, Charset encoding) {
        ClassLoader classLoader = Provider.class.getClassLoader();
        return resourceProvider(classLoader, pathToResource, encoding);
    }

    public static Provider resourceProvider(String pathToResource) {
        return resourceProvider(pathToResource, UTF8);
    }

}
