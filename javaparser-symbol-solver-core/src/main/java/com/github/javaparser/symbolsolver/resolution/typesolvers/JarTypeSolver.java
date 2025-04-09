/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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
import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.stream.Stream;
import javassist.ClassPool;
import javassist.NotFoundException;

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
     * @param pathToJarOrClassFileHierarchy The path where the jar or class file hierarchy is located.
     *
     * @throws IOException If an I/O exception occurs while reading the Jar or class file hierarchy.
     */
    public JarTypeSolver(Path pathToJarOrClassFileHierarchy) throws IOException {
        this(pathToJarOrClassFileHierarchy.toFile());
    }

    /**
     * Create a {@link JarTypeSolver} from a {@link File}.
     *
     * @param pathToJarOrClassFileHierarchy The file pointing to the jar or class file hierarchy is located.
     *
     * @throws IOException If an I/O exception occurs while reading the Jar or class file hierarchy.
     */
    public JarTypeSolver(File pathToJarOrClassFileHierarchy) throws IOException {
        this(pathToJarOrClassFileHierarchy.getAbsolutePath());
    }

    /**
     * Create a {@link JarTypeSolver} from a path in a {@link String} format.
     *
     * @param pathToJarOrClassFileHierarchy The path pointing to the jar or class file hierarchy.
     *
     * @throws IOException If an I/O exception occurs while reading the Jar or class file hierarchy.
     */
    public JarTypeSolver(String pathToJarOrClassFileHierarchy) throws IOException {
        addPathToJar(pathToJarOrClassFileHierarchy);
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
     * @param pathToJarOrClassFileHierarchy The path pointing to the jar file or class file hierarchy.
     *
     * @throws IOException If an I/O error occurs while reading the JarFile or class file hierarchy.
     */
    private void addPathToJar(String pathToJarOrClassFileHierarchy) throws IOException {
        try {
            classPool.appendClassPath(pathToJarOrClassFileHierarchy);
            registerKnownClassesFor(pathToJarOrClassFileHierarchy);
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
     * @param pathToJarOrClassFileHierarchy The path to the jar file or .class file hierarchy.
     *
     * @throws IOException If an I/O error occurs while reading the JarFile or .class file hierarchy.
     */
    private void registerKnownClassesFor(String pathToJarOrClassFileHierarchy) throws IOException {
        Path jarOrClassFileHierarchy = Paths.get(pathToJarOrClassFileHierarchy);
        if (Files.isDirectory(jarOrClassFileHierarchy)) {
            try (Stream<Path> classFiles = Files.walk(jarOrClassFileHierarchy)) {
                classFiles
                        .filter(path -> Files.isRegularFile(path)
                                && path.getFileName().toString().endsWith(CLASS_EXTENSION))
                        .forEach(pathToClassFile -> {
                            // We can't just use path.toString here, since path seperators are OS-dependent.
                            String packagePrefix = convertPathToPackagePrefix(jarOrClassFileHierarchy, pathToClassFile);
                            String classFileName = pathToClassFile.getFileName().toString();
                            String classNameWithDollars =
                                    classFileName.substring(0, classFileName.length() - CLASS_EXTENSION.length());
                            String classPoolName = packagePrefix + classNameWithDollars;
                            String qualifiedName = packagePrefix + classNameWithDollars.replace('$', '.');

                            // If the qualified name is the same as the class pool name we don't need to duplicate store
                            // two
                            // different String instances. Let's reuse the same.
                            if (qualifiedName.equals(classPoolName)) {
                                knownClasses.put(qualifiedName, qualifiedName);
                            } else {
                                knownClasses.put(qualifiedName, classPoolName);
                            }
                        });
            }
        } else if (Files.isRegularFile(jarOrClassFileHierarchy)) {
            try (JarFile jarFile = new JarFile(pathToJarOrClassFileHierarchy)) {

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
    }

    /**
     * Given a path to a class file inside a class file hierarchy, extract the package name from the path.
     * @param pathToClassFileHierarchy the root of the class file hierarchy
     * @param pathToClassFile the path to the class file, inside the hierarchy
     * @return the package name of the class file
     */
    private static String convertPathToPackagePrefix(Path pathToClassFileHierarchy, Path pathToClassFile) {
        Path packagePath = pathToClassFileHierarchy.relativize(pathToClassFile).getParent();
        StringBuilder packagePrefixBuilder = new StringBuilder();
        if (packagePath != null) {
            for (Path component : packagePath) {
                packagePrefixBuilder.append(component.toString()).append('.');
            }
        }
        return packagePrefixBuilder.toString();
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
                    "Unable to get class with name %s from class pool."
                            + "This was not suppose to happen, please report at https://github.com/javaparser/javaparser/issues",
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
