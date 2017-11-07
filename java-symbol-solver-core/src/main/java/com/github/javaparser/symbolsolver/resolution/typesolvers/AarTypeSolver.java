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
import java.util.jar.JarFile;
import java.util.zip.ZipEntry;

/**
 * @author Federico Tomassetti
 */
public class AarTypeSolver implements TypeSolver {

    private TypeSolver parent;
    private File aarFile;
    private JarTypeSolver delegate;

    public AarTypeSolver(File aarFile) throws IOException {
        this.aarFile = aarFile;

        JarFile jarFile = new JarFile(aarFile);
        ZipEntry classesJarEntry = jarFile.getEntry("classes.jar");
        if (classesJarEntry == null) {
            throw new IllegalArgumentException(String.format("The given file (%s) is malformed: entry classes.jar was not found", aarFile.getAbsolutePath()));
        }
        delegate = new JarTypeSolver(jarFile.getInputStream(classesJarEntry));
    }

    @Override
    public TypeSolver getParent() {
        return parent;
    }

    @Override
    public void setParent(TypeSolver parent) {
        this.parent = parent;
    }

    @Override
    public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
        return delegate.tryToSolveType(name);
    }
}
