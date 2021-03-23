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

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import javassist.ClassPool;
import javassist.NotFoundException;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.Path;
import java.util.Objects;
import java.util.Optional;

/**
 * Will let the symbol solver look inside a jar file while solving types.
 *
 * @author Federico Tomassetti
 */
public class JarTypeSolver implements TypeSolver {

    /**
     * @deprecated Use of this static method (previously following singleton pattern) is strongly discouraged
     * and will be removed in a future version. For now, it has been modified to return a new instance to
     * prevent the IllegalStateException being thrown (as reported in #2547), allowing it to be called multiple times.
     */
    @Deprecated
    public static JarTypeSolver getJarTypeSolver(String pathToJar) throws IOException {
        return new JarTypeSolver(pathToJar);
    }

    private final ClassPool classPool = new ClassPool();

    private TypeSolver parent;

    /**
     * Create a {@link JarTypeSolver} from a {@link Path}.
     *
     * @param pathToJar The path where the jar is located.
     *
     * @throws FileNotFoundException If the jar file was not found.
     */
    public JarTypeSolver(Path pathToJar) throws FileNotFoundException {
        this(pathToJar.toFile());
    }

    /**
     * Create a {@link JarTypeSolver} from a {@link File}.
     *
     * @param pathToJar The file pointing to the jar is located.
     *
     * @throws FileNotFoundException If the jar file was not found.
     */
    public JarTypeSolver(File pathToJar) throws FileNotFoundException {
        this(pathToJar.getAbsolutePath());
    }

    /**
     * Create a {@link JarTypeSolver} from a path in a {@link String} format.
     *
     * @param pathToJar The path pointing to the jar.
     *
     * @throws FileNotFoundException If the jar file was not found.
     */
    public JarTypeSolver(String pathToJar) throws FileNotFoundException {
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
     * @throws FileNotFoundException If the jar file was not found.
     */
    private void addPathToJar(String pathToJar) throws FileNotFoundException {
        try {
            classPool.appendClassPath(pathToJar);
        } catch (NotFoundException e) {
            // If JavaAssist throws a NotFoundException we should notify the user
            // with a FileNotFoundException.
            FileNotFoundException jarNotFound = new FileNotFoundException(e.getMessage());
            jarNotFound.initCause(e);
            throw jarNotFound;
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

    @Override
    public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
        try {
            return SymbolReference.solved(JavassistFactory.toTypeDeclaration(classPool.get(name), getRoot()));
        } catch (NotFoundException e) {
            // it could be an inner class
            int lastDot = name.lastIndexOf('.');
            if (lastDot == -1) {
                return SymbolReference.unsolved(ResolvedReferenceTypeDeclaration.class);
            } else {
                String parentName = name.substring(0, lastDot);
                String childName = name.substring(lastDot + 1);
                SymbolReference<ResolvedReferenceTypeDeclaration> parent = tryToSolveType(parentName);
                if (parent.isSolved()) {
                    Optional<ResolvedReferenceTypeDeclaration> innerClass = parent.getCorrespondingDeclaration()
                            .internalTypes()
                            .stream().filter(it -> it.getName().equals(childName)).findFirst();
                    return innerClass.map(SymbolReference::solved)
                            .orElseGet(() -> SymbolReference.unsolved(ResolvedReferenceTypeDeclaration.class));
                } else {
                    return SymbolReference.unsolved(ResolvedReferenceTypeDeclaration.class);
                }
            }
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

}
