/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

package org.javaparser.symbolsolver.resolution.typesolvers;

import org.javaparser.resolution.UnsolvedSymbolException;
import org.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import org.javaparser.symbolsolver.javassistmodel.JavassistFactory;
import org.javaparser.symbolsolver.model.resolution.SymbolReference;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.NotFoundException;

import java.io.*;
import java.nio.file.Path;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

/**
 * Will let the symbol solver look inside a jar file while solving types.
 *
 * @author Federico Tomassetti
 */
public class JarTypeSolver implements TypeSolver {

    private static JarTypeSolver instance;

    private TypeSolver parent;
    private Map<String, ClasspathElement> classpathElements = new HashMap<>();
    private ClassPool classPool = new ClassPool(false);

    public JarTypeSolver(Path pathToJar) throws IOException {
        this(pathToJar.toFile());
    }

    public JarTypeSolver(File pathToJar) throws IOException {
        this(pathToJar.getCanonicalPath());
    }

    public JarTypeSolver(String pathToJar) throws IOException {
        addPathToJar(pathToJar);
    }

    public JarTypeSolver(InputStream jarInputStream) throws IOException {
        addPathToJar(jarInputStream);
    }

    public static JarTypeSolver getJarTypeSolver(String pathToJar) throws IOException {
        if (instance == null) {
            instance = new JarTypeSolver(pathToJar);
        } else {
            instance.addPathToJar(pathToJar);
        }
        return instance;
    }

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

    private void addPathToJar(InputStream jarInputStream) throws IOException {
        addPathToJar(dumpToTempFile(jarInputStream).getAbsolutePath());
    }

    private void addPathToJar(String pathToJar) throws IOException {
        try {
            classPool.appendClassPath(pathToJar);
            classPool.appendSystemPath();
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
        JarFile jarFile = new JarFile(pathToJar);
        JarEntry entry;
        Enumeration<JarEntry> e = jarFile.entries();
        while (e.hasMoreElements()) {
            entry = e.nextElement();
            if (entry != null && !entry.isDirectory() && entry.getName().endsWith(".class")) {
                String name = entryPathToClassName(entry.getName());
                classpathElements.put(name, new ClasspathElement(jarFile, entry));
            }
        }
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

    private String entryPathToClassName(String entryPath) {
        if (!entryPath.endsWith(".class")) {
            throw new IllegalStateException();
        }
        String className = entryPath.substring(0, entryPath.length() - ".class".length());
        className = className.replace('/', '.');
        className = className.replace('$', '.');
        return className;
    }

    @Override
    public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
        try {
            if (classpathElements.containsKey(name)) {
                return SymbolReference.solved(
                        JavassistFactory.toTypeDeclaration(classpathElements.get(name).toCtClass(), getRoot()));
            } else {
                return SymbolReference.unsolved(ResolvedReferenceTypeDeclaration.class);
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ResolvedReferenceTypeDeclaration solveType(String name) throws UnsolvedSymbolException {
        SymbolReference<ResolvedReferenceTypeDeclaration> ref = tryToSolveType(name);
        if (ref.isSolved()) {
            return ref.getCorrespondingDeclaration();
        } else {
            throw new UnsolvedSymbolException(name);
        }
    }

    private class ClasspathElement {
        private JarFile jarFile;
        private JarEntry entry;

        ClasspathElement(JarFile jarFile, JarEntry entry) {
            this.jarFile = jarFile;
            this.entry = entry;
        }

        CtClass toCtClass() throws IOException {
            try (InputStream is = jarFile.getInputStream(entry)) {
                return classPool.makeClass(is);
            }
        }
    }
}
