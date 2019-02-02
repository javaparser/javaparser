/*
 * Copyright 2017 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.jar.JarFile;
import java.util.zip.ZipEntry;

/**
 * Will let the symbol solver look inside an Android aar file while solving types.
 * (It will look inside the contained classes.jar)
 *
 * @author Federico Tomassetti
 */
public class AarTypeSolver implements TypeSolver {

    private JarTypeSolver delegate;

    public AarTypeSolver(String aarFile) throws IOException {
        this(new File(aarFile));
    }

    public AarTypeSolver(Path aarFile) throws IOException {
        this(aarFile.toFile());
    }

    public AarTypeSolver(File aarFile) throws IOException {
        JarFile jarFile = new JarFile(aarFile);
        ZipEntry classesJarEntry = jarFile.getEntry("classes.jar");
        if (classesJarEntry == null) {
            throw new IllegalArgumentException(String.format("The given file (%s) is malformed: entry classes.jar was not found", aarFile.getAbsolutePath()));
        }
        delegate = new JarTypeSolver(jarFile.getInputStream(classesJarEntry));
    }

    @Override
    public TypeSolver getParent() {
        return delegate.getParent();
    }

    @Override
    public void setParent(TypeSolver parent) {
        delegate.setParent(parent);
    }

    @Override
    public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
        return delegate.tryToSolveType(name);
    }
}
