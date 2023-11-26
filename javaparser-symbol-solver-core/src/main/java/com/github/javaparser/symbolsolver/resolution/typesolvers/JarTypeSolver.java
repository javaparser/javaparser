/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistFactory;
import javassist.ClassPool;
import javassist.NotFoundException;

import java.io.*;
import java.nio.file.Path;
import java.util.*;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

/**
 * Will let the symbol solver look inside a jar file while solving types.
 *
 * @author Federico Tomassetti
 */
public class JarTypeSolver implements TypeSolver {

    private static final String CLASS_EXTENSION = ".class";

    /**
     * @deprecated Use of this static method (previously following singleton pattern) is strongly discouraged
     * and will be removed in a future version. For now, it has been modified to return a new instance to
     * prevent the IllegalStateException being thrown (as reported in #2547), allowing it to be called multiple times.
     */
    @Deprecated
    public static JarTypeSolver getJarTypeSolver(String pathToJar) throws IOException {
        return new JarTypeSolver(pathToJar);
    }

    /**
     * Convert the entry path into a qualified name.
     *
     * The entries in Jar files follows the format {@code com/github/javaparser/ASTParser$JJCalls.class}
     * while in the type solver we need to work with {@code com.github.javaparser.ASTParser.JJCalls}.
     *
     * @param entryPath The entryPath to be converted.
     *
     * @return The qualified name for the entryPath.
     */
    private static String convertEntryPathToClassName(String entryPath) {
        if (!entryPath.endsWith(CLASS_EXTENSION)) {
            throw new IllegalArgumentException(String.format("The entry path should end with %s", CLASS_EXTENSION));
        }
        String className = entryPath.substring(0, entryPath.length() - CLASS_EXTENSION.length());
        className = className.replace('/', '.');
        className = className.replace('$', '.');
        return className;
    }

    /**
     * Convert the entry path into a qualified name to be used in {@link ClassPool}.
     *
     * The entries in Jar files follows the format {@code com/github/javaparser/ASTParser$JJCalls.class}
     * while in the class pool we need to work with {@code com.github.javaparser.ASTParser$JJCalls}.
     *
     * @param entryPath The entryPath to be converted.
     *
     * @return The qualified name to be used in the class pool.
     */
    private static String convertEntryPathToClassPoolName(String entryPath) {
        if (!entryPath.endsWith(CLASS_EXTENSION)) {
            throw new IllegalArgumentException(String.format("The entry path should end with %s", CLASS_EXTENSION));
        }
        String className = entryPath.substring(0, entryPath.length() - CLASS_EXTENSION.length());
        return className.replace('/', '.');
    }

    private final ClassPool classPool = new ClassPool();
    private final Map<String, String> knownClasses = new HashMap<>();

    private TypeSolver parent;

    /**
     * Create a {@link JarTypeSolver} from a {@link Path}.
     *
     * @param pathToJar The path where the jar is located.
     *
     * @throws IOException If an I/O exception occurs while reading the Jar.
     */
    public JarTypeSolver(Path pathToJar) throws IOException {
        this(pathToJar.toFile());
    }

    /**
     * Create a {@link JarTypeSolver} from a {@link File}.
     *
     * @param pathToJar The file pointing to the jar is located.
     *
     * @throws IOException If an I/O exception occurs while reading the Jar.
     */
    public JarTypeSolver(File pathToJar) throws IOException {
        this(pathToJar.getAbsolutePath());
    }

    /**
     * Create a {@link JarTypeSolver} from a path in a {@link String} format.
     *
     * @param pathToJar The path pointing to the jar.
     *
     * @throws IOException If an I/O exception occurs while reading the Jar.
     */
    public JarTypeSolver(String pathToJar) throws IOException {
        addPathToJar(pathToJar);
    }

    /**
     * Create a {@link JarTypeSolver} from a {@link InputStream}.
     *
     * The content will be dumped into a temporary file to be used in the type solver.
     *
     * @param jarInputStream The input stream to be used.
     *
     * @throws IOException If an I/O exception occurs while creating the temporary file.
     */
    public JarTypeSolver(InputStream jarInputStream) throws IOException {
        addPathToJar(dumpToTempFile(jarInputStream).getAbsolutePath());
    }

    /**
     * Utility function to dump the input stream into a temporary file.
     *
     * This file will be deleted when the virtual machine terminates.
     *
     * @param inputStream The input to be dumped.
     *
     * @return The created file with the dumped information.
     *
     * @throws IOException If an I/O exception occurs while creating the temporary file.
     */
    private File dumpToTempFile(InputStream inputStream) throws IOException {
        File tempFile = File.createTempFile("jar_file_from_input_stream", ".jar");
        tempFile.deleteOnExit();

        byte[] buffer = new byte[8 * 1024];

        try (OutputStream output = new FileOutputStream(tempFile)) {
            int bytesRead;
            while ((bytesRead = inputStream.read(buffer)) != -1) {
                output.write(buffer, 0, bytesRead);
            }
        } finally {
            inputStream.close();
        }
        return tempFile;
    }

    /**
     * Utility method to register a new class path.
     *
     * @param pathToJar The path pointing to the jar file.
     *
     * @throws IOException If an I/O error occurs while reading the JarFile.
     */
    private void addPathToJar(String pathToJar) throws IOException {
        try {
            classPool.appendClassPath(pathToJar);
            registerKnownClassesFor(pathToJar);
        } catch (NotFoundException e) {
            // If JavaAssist throws a NotFoundException we should notify the user
            // with a FileNotFoundException.
            FileNotFoundException jarNotFound = new FileNotFoundException(e.getMessage());
            jarNotFound.initCause(e);
            throw jarNotFound;
        }
    }

    /**
     * Register the list of known classes.
     *
     * When we create a new {@link JarTypeSolver} we should store the list of
     * solvable types.
     *
     * @param pathToJar The path to the jar file.
     *
     * @throws IOException If an I/O error occurs while reading the JarFile.
     */
    private void registerKnownClassesFor(String pathToJar) throws IOException {
        try (JarFile jarFile = new JarFile(pathToJar)) {

            Enumeration<JarEntry> jarEntries = jarFile.entries();
            while (jarEntries.hasMoreElements()) {

                JarEntry entry = jarEntries.nextElement();
                // Check if the entry is a .class file
                if (!entry.isDirectory() && entry.getName().endsWith(CLASS_EXTENSION)) {
                    String qualifiedName = convertEntryPathToClassName(entry.getName());
                    String classPoolName = convertEntryPathToClassPoolName(entry.getName());

                    // If the qualified name is the same as the class pool name we don't need to duplicate store two
                    // different String instances. Let's reuse the same.
                    if (qualifiedName.equals(classPoolName)) {
                        knownClasses.put(qualifiedName, qualifiedName);
                    } else {
                        knownClasses.put(qualifiedName, classPoolName);
                    }
                }
            }

        }
    }

    /**
     * Get the set of classes that can be resolved in the current type solver.
     *
     * @return The set of known classes.
     */
    public Set<String> getKnownClasses() {
        return knownClasses.keySet();
    }

    @Override
    public TypeSolver getParent() {
        return parent;
    }

    @Override
    public void setParent(TypeSolver parent) {
        Objects.requireNonNull(parent);
        if (this.parent != null) {
            throw new IllegalStateException("This TypeSolver already has a parent.");
        }
        if (parent == this) {
            throw new IllegalStateException("The parent of this TypeSolver cannot be itself.");
        }
        this.parent = parent;
    }

    @Override
    public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {

        String storedKey = knownClasses.get(name);
        // If the name is not registered in the list we can safely say is not solvable here
        if (storedKey == null) {
            return SymbolReference.unsolved();
        }

        try {
            return SymbolReference.solved(JavassistFactory.toTypeDeclaration(classPool.get(storedKey), getRoot()));
        } catch (NotFoundException e) {
            // The names in stored key should always be resolved.
            // But if for some reason this happen, the user is notified.
            throw new IllegalStateException(String.format(
                    "Unable to get class with name %s from class pool." +
                    "This was not suppose to happen, please report at https://github.com/javaparser/javaparser/issues",
                    storedKey));
        }
    }

    @Override
    public ResolvedReferenceTypeDeclaration solveType(String name) throws UnsolvedSymbolException {
        SymbolReference<ResolvedReferenceTypeDeclaration> ref = tryToSolveType(name);
        if (ref.isSolved()) {
            return ref.getCorrespondingDeclaration();
        }
        throw new UnsolvedSymbolException(name);
    }

}
