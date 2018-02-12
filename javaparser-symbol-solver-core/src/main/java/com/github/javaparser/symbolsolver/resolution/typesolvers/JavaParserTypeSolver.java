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
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;

/**
 * @author Federico Tomassetti
 */
public class JavaParserTypeSolver implements TypeSolver {

    private File srcDir;

    private TypeSolver parent;

    private Cache<String, Optional<CompilationUnit>> parsedFiles = CacheBuilder.newBuilder().softValues().build();
    private Cache<String, List<CompilationUnit>> parsedDirectories = CacheBuilder.newBuilder().softValues().build();
    private Cache<String, SymbolReference<ResolvedReferenceTypeDeclaration>> foundTypes = CacheBuilder.newBuilder().softValues().build();

    public JavaParserTypeSolver(File srcDir) {
        if (!srcDir.exists() || !srcDir.isDirectory()) {
            throw new IllegalStateException("SrcDir does not exist or is not a directory: " + srcDir.getAbsolutePath());
        }
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


    private Optional<CompilationUnit> parse(File srcFile) {
        try {
            return parsedFiles.get(srcFile.getAbsolutePath(), () -> {
                Optional<CompilationUnit> cu;
                try {
                    cu = Optional.of(JavaParser.parse(srcFile));
                } catch (FileNotFoundException e) {
                    cu = Optional.empty();
                } catch (RuntimeException e) {
                    throw new RuntimeException("Issue while parsing " + srcFile.getAbsolutePath(), e);
                }
                return cu;
            });
        } catch (ExecutionException e) {
            throw new RuntimeException(e);
        }
    }

    private List<CompilationUnit> parseDirectory(File srcDirectory) {
        try {
            return parsedDirectories.get(srcDirectory.getAbsolutePath(), () -> {
                List<CompilationUnit> units = new ArrayList<>();
                File[] files = srcDirectory.listFiles();
                if (files != null) {
                    for (File file : files) {
                        if (file.getName().toLowerCase().endsWith(".java")) {
                            Optional<CompilationUnit> unit = parse(file);
                            if (unit.isPresent()) {
                                units.add(unit.get());
                            }
                        }
                    }
                }
                return units;
            });
        } catch (ExecutionException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
        // TODO support enums
        // TODO support interfaces
        try {
            return foundTypes.get(name, () -> {
                SymbolReference<ResolvedReferenceTypeDeclaration> result = tryToSolveTypeUncached(name);
                if (result.isSolved()) {
                    return SymbolReference.solved(result.getCorrespondingDeclaration());
                }
                return result;
            });
        } catch (ExecutionException e) {
            throw new RuntimeException(e);
        }
    }

    private SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveTypeUncached(String name) {
        String[] nameElements = name.split("\\.");

        for (int i = nameElements.length; i > 0; i--) {
            String filePath = srcDir.getAbsolutePath();
            for (int j = 0; j < i; j++) {
                filePath += "/" + nameElements[j];
            }
            filePath += ".java";

            String typeName = "";
            for (int j = i - 1; j < nameElements.length; j++) {
                if (j != i - 1) {
                    typeName += ".";
                }
                typeName += nameElements[j];
            }

            File srcFile = new File(filePath);
            {
                Optional<CompilationUnit> compilationUnit = parse(srcFile);
                if (compilationUnit.isPresent()) {
                    Optional<com.github.javaparser.ast.body.TypeDeclaration<?>> astTypeDeclaration = Navigator.findType(compilationUnit.get(), typeName);
                    if (astTypeDeclaration.isPresent()) {
                        return SymbolReference.solved(JavaParserFacade.get(this).getTypeDeclaration(astTypeDeclaration.get()));
                    }
                }
            }

            {
                List<CompilationUnit> compilationUnits = parseDirectory(srcFile.getParentFile());
                for (CompilationUnit compilationUnit : compilationUnits) {
                    Optional<com.github.javaparser.ast.body.TypeDeclaration<?>> astTypeDeclaration = Navigator.findType(compilationUnit, typeName);
                    if (astTypeDeclaration.isPresent()) {
                        return SymbolReference.solved(JavaParserFacade.get(this).getTypeDeclaration(astTypeDeclaration.get()));
                    }
                }
            }
        }

        return SymbolReference.unsolved(ResolvedReferenceTypeDeclaration.class);
    }

}
