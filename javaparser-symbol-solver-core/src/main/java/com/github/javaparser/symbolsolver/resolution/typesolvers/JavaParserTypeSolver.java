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
import com.github.javaparser.ParserConfiguration;
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
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.ExecutionException;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static com.github.javaparser.Providers.provider;

/**
 * Defines a directory containing source code that should be used for solving symbols.
 * The directory must correspond to the root package of the files within.
 *
 * @author Federico Tomassetti
 */
public class JavaParserTypeSolver implements TypeSolver {

    private final Path srcDir;
    private final JavaParser javaParser;

    private TypeSolver parent;

    private final Cache<Path, Optional<CompilationUnit>> parsedFiles = CacheBuilder.newBuilder().softValues().build();
    private final Cache<Path, List<CompilationUnit>> parsedDirectories = CacheBuilder.newBuilder().softValues().build();
    private final Cache<String, SymbolReference<ResolvedReferenceTypeDeclaration>> foundTypes = CacheBuilder.newBuilder().softValues().build();

    public JavaParserTypeSolver(File srcDir) {
        this(srcDir.toPath());
    }

    public JavaParserTypeSolver(String srcDir) {
        this(new File(srcDir));
    }

    public JavaParserTypeSolver(File srcDir, ParserConfiguration parserConfiguration) {
        this(srcDir.toPath(), parserConfiguration);
    }

    public JavaParserTypeSolver(String srcDir, ParserConfiguration parserConfiguration) {
        this(new File(srcDir), parserConfiguration);
    }

    public JavaParserTypeSolver(Path srcDir, ParserConfiguration parserConfiguration) {
        if (!Files.exists(srcDir) || !Files.isDirectory(srcDir)) {
            throw new IllegalStateException("SrcDir does not exist or is not a directory: " + srcDir);
        }
        this.srcDir = srcDir;
        javaParser = new JavaParser(parserConfiguration);
    }

    public JavaParserTypeSolver(Path srcDir) {
        this(srcDir,
                new ParserConfiguration()
                        .setLanguageLevel(BLEEDING_EDGE));
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

    private Optional<CompilationUnit> parse(Path srcFile) {
        try {
            return parsedFiles.get(srcFile.toAbsolutePath(), () -> {
                try {
                    if (!Files.exists(srcFile) || !Files.isRegularFile(srcFile)) {
                        return Optional.empty();
                    }
                    return javaParser.parse(COMPILATION_UNIT, provider(srcFile))
                            .getResult()
                            .map(cu -> cu.setStorage(srcFile));
                } catch (FileNotFoundException e) {
                    throw new RuntimeException("Issue while parsing while type solving: " + srcFile.toAbsolutePath(), e);
                }
            });
        } catch (ExecutionException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Note that this parse only files directly contained in this directory.
     * It does not traverse recursively all children directory.
     */
    private List<CompilationUnit> parseDirectory(Path srcDirectory) {
        return parseDirectory(srcDirectory, false);
    }

    private List<CompilationUnit> parseDirectoryRecursively(Path srcDirectory) {
        return parseDirectory(srcDirectory, true);
    }

    private List<CompilationUnit> parseDirectory(Path srcDirectory, boolean recursively) {
        try {
            return parsedDirectories.get(srcDirectory.toAbsolutePath(), () -> {
                List<CompilationUnit> units = new ArrayList<>();
                if(Files.exists(srcDirectory)) {
                    try (DirectoryStream<Path> srcDirectoryStream = Files.newDirectoryStream(srcDirectory)) {
                        srcDirectoryStream
                                .forEach(file -> {
                                    if (file.getFileName().toString().toLowerCase().endsWith(".java")) {
                                        parse(file).ifPresent(units::add);
                                    } else if (recursively && file.toFile().isDirectory()) {
                                        units.addAll(parseDirectoryRecursively(file));
                                    }
                                });
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
            StringBuilder filePath = new StringBuilder(srcDir.toAbsolutePath().toString());
            for (int j = 0; j < i; j++) {
                filePath.append("/")
                        .append(nameElements[j]);
            }
            filePath.append(".java");

            StringBuilder typeName = new StringBuilder();
            for (int j = i - 1; j < nameElements.length; j++) {
                if (j != i - 1) {
                    typeName.append(".");
                }
                typeName.append(nameElements[j]);
            }

            // As an optimization we first try to look in the canonical position where we expect to find the file
            Path srcFile = Paths.get(filePath.toString());
            {
                Optional<CompilationUnit> compilationUnit = parse(srcFile);
                if (compilationUnit.isPresent()) {
                    Optional<com.github.javaparser.ast.body.TypeDeclaration<?>> astTypeDeclaration = Navigator.findType(compilationUnit.get(), typeName.toString());
                    if (astTypeDeclaration.isPresent()) {
                        return SymbolReference.solved(JavaParserFacade.get(this).getTypeDeclaration(astTypeDeclaration.get()));
                    }
                }
            }

            // If this is not possible we parse all files
            // We try just in the same package, for classes defined in a file not named as the class itself
            {
                List<CompilationUnit> compilationUnits = parseDirectory(srcFile.getParent());
                for (CompilationUnit compilationUnit : compilationUnits) {
                    Optional<com.github.javaparser.ast.body.TypeDeclaration<?>> astTypeDeclaration = Navigator.findType(compilationUnit, typeName.toString());
                    if (astTypeDeclaration.isPresent()) {
                        return SymbolReference.solved(JavaParserFacade.get(this).getTypeDeclaration(astTypeDeclaration.get()));
                    }
                }
            }
        }

        return SymbolReference.unsolved(ResolvedReferenceTypeDeclaration.class);
    }

}
