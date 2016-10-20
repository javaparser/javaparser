/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class JavaParserTypeSolver implements TypeSolver {

    private File srcDir;

    private TypeSolver parent;

    private Map<String, CompilationUnit> parsedFiles = new HashMap<String, CompilationUnit>();

    public JavaParserTypeSolver(File srcDir) {
        this.srcDir = srcDir;
    }

    @Override
    public String toString() {
        return "JavaParserTypeSolver{" +
                "srcDir=" + srcDir +
                ", parent=" + parent +
                '}';
    }

    @Override
    public TypeSolver getParent() {
        return parent;
    }

    @Override
    public void setParent(TypeSolver parent) {
        this.parent = parent;
    }


    private CompilationUnit parse(File srcFile) throws FileNotFoundException {
        if (!parsedFiles.containsKey(srcFile.getAbsolutePath())) {
            parsedFiles.put(srcFile.getAbsolutePath(), JavaParser.parse(srcFile));
        }
        return parsedFiles.get(srcFile.getAbsolutePath());
    }

    @Override
    public SymbolReference<TypeDeclaration> tryToSolveType(String name) {
        if (!srcDir.exists() || !srcDir.isDirectory()) {
            throw new IllegalStateException("SrcDir does not exist or is not a directory: " + srcDir.getAbsolutePath());
        }

        // TODO support enums
        // TODO support interfaces

        String[] nameElements = name.split("\\.");

        for (int i = nameElements.length; i > 0; i--) {
            String filePath = srcDir.getAbsolutePath();
            for (int j = 0; j < i; j++) {
                filePath += "/" + nameElements[j];
            }
            filePath += ".java";

            File srcFile = new File(filePath);
            if (srcFile.exists()) {
                try {
                    String typeName = "";
                    for (int j = i - 1; j < nameElements.length; j++) {
                        if (j != i - 1) {
                            typeName += ".";
                        }
                        typeName += nameElements[j];
                    }
                    CompilationUnit compilationUnit = parse(srcFile);
                    Optional<com.github.javaparser.ast.body.TypeDeclaration<?>> astTypeDeclaration = Navigator.findType(compilationUnit, typeName);
                    if (!astTypeDeclaration.isPresent()) {
                        return SymbolReference.unsolved(TypeDeclaration.class);
                    }
                    TypeDeclaration typeDeclaration = JavaParserFacade.get(this).getTypeDeclaration(astTypeDeclaration.get());
                    return SymbolReference.solved(typeDeclaration);
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
            }
        }

        return SymbolReference.unsolved(TypeDeclaration.class);
    }

}
