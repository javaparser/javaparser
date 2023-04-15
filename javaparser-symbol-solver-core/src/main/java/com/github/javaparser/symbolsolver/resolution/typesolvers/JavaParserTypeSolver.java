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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.cache.Cache;
import com.github.javaparser.symbolsolver.cache.GuavaCache;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.utils.FileUtils;
import com.google.common.cache.CacheBuilder;

import java.io.File;
import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

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

    private final Cache<Path, Optional<CompilationUnit>> parsedFiles;
    private final Cache<Path, List<CompilationUnit>> parsedDirectories;
    private final Cache<String, SymbolReference<ResolvedReferenceTypeDeclaration>> foundTypes;
    private static final int CACHE_SIZE_UNSET = -1;

    public JavaParserTypeSolver(File srcDir) {
        this(srcDir.toPath());
    }

    public JavaParserTypeSolver(String srcDir) {
        this(new File(srcDir));
    }

    public JavaParserTypeSolver(Path srcDir) {
        this(srcDir, new ParserConfiguration().setLanguageLevel(BLEEDING_EDGE));
    }

    public JavaParserTypeSolver(File srcDir, ParserConfiguration parserConfiguration) {
        this(srcDir.toPath(), parserConfiguration);
    }

    public JavaParserTypeSolver(String srcDir, ParserConfiguration parserConfiguration) {
        this(new File(srcDir), parserConfiguration);
    }

    public JavaParserTypeSolver(Path srcDir, ParserConfiguration parserConfiguration) {
        this(srcDir, parserConfiguration, CACHE_SIZE_UNSET);
    }

    private <TKey, TValue> Cache<TKey, TValue> BuildCache(long cacheSizeLimit) {
        CacheBuilder<Object, Object> cacheBuilder = CacheBuilder.newBuilder().softValues();
        if (cacheSizeLimit != CACHE_SIZE_UNSET) {
            cacheBuilder.maximumSize(cacheSizeLimit);
        }
        return new GuavaCache<>(cacheBuilder.build());
    }

    /**
     * @param srcDir is the source code directory for the type solver.
     * @param parserConfiguration is the configuration the solver should use when inspecting source code files.
     * @param cacheSizeLimit is an optional size limit to the internal caches used by this solver.
     *        Be advised that setting the size too low might lead to noticeable performance degradation.
     *        However, using a size limit is advised when solving symbols in large code sources. In such cases, internal caches might consume large amounts of heap space.
     */
    public JavaParserTypeSolver(Path srcDir, ParserConfiguration parserConfiguration, long cacheSizeLimit) {
        if (!Files.exists(srcDir) || !Files.isDirectory(srcDir)) {
            throw new IllegalStateException("SrcDir does not exist or is not a directory: " + srcDir);
        }
        this.srcDir = srcDir;
        javaParser = new JavaParser(parserConfiguration);
        parsedFiles = BuildCache(cacheSizeLimit);
        parsedDirectories = BuildCache(cacheSizeLimit);
        foundTypes = BuildCache(cacheSizeLimit);
    }

    /**
     * Create a {@link JavaParserTypeSolver} with a custom cache system.
     *
     * @param srcDir                    The source code directory for the type solver.
     * @param javaParser                The {@link JavaParser} to be used when parsing .java files.
     * @param parsedFilesCache          The cache to be used to store {@link CompilationUnit} that is associated with
     *                                  a file.
     * @param parsedDirectoriesCache    The cache to store the list of {@link CompilationUnit} in a given directory.
     * @param foundTypesCache           The cache that associated a qualified name to its {@link SymbolReference}.
     */
    public JavaParserTypeSolver(Path srcDir,
                                JavaParser javaParser,
                                Cache<Path, Optional<CompilationUnit>> parsedFilesCache,
                                Cache<Path, List<CompilationUnit>> parsedDirectoriesCache,
                                Cache<String, SymbolReference<ResolvedReferenceTypeDeclaration>> foundTypesCache) {
        Objects.requireNonNull(srcDir, "The srcDir can't be null.");
        Objects.requireNonNull(javaParser, "The javaParser can't be null.");
        Objects.requireNonNull(parsedFilesCache, "The parsedFilesCache can't be null.");
        Objects.requireNonNull(parsedDirectoriesCache, "The parsedDirectoriesCache can't be null.");
        Objects.requireNonNull(foundTypesCache, "The foundTypesCache can't be null.");

        if (!Files.exists(srcDir) || !Files.isDirectory(srcDir)) {
            throw new IllegalStateException("SrcDir does not exist or is not a directory: " + srcDir);
        }

        this.srcDir = srcDir;
        this.javaParser = javaParser;
        this.parsedFiles = parsedFilesCache;
        this.parsedDirectories = parsedDirectoriesCache;
        this.foundTypes = foundTypesCache;
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
        Objects.requireNonNull(parent);
        if (this.parent != null) {
            throw new IllegalStateException("This TypeSolver already has a parent.");
        }
        if (parent == this) {
            throw new IllegalStateException("The parent of this TypeSolver cannot be itself.");
        }
        this.parent = parent;
    }

    private Optional<CompilationUnit> parse(Path srcFile) {
        try {
            Optional<Optional<CompilationUnit>> cachedParsedFile = parsedFiles.get(srcFile.toAbsolutePath());
            // If the value is already cached
            if (cachedParsedFile.isPresent()) {
                return cachedParsedFile.get();
            }

            // Otherwise load it
            if (!Files.exists(srcFile) || !Files.isRegularFile(srcFile)) {
                parsedFiles.put(srcFile.toAbsolutePath(), Optional.empty());
                return Optional.empty();
            }

            // JavaParser only allow one parse at time.
            synchronized (javaParser) {
                Optional<CompilationUnit> compilationUnit = javaParser.parse(COMPILATION_UNIT, provider(srcFile, javaParser.getParserConfiguration().getCharacterEncoding()))
                        .getResult()
                        .map(cu -> cu.setStorage(srcFile));
                parsedFiles.put(srcFile.toAbsolutePath(), compilationUnit);
                return compilationUnit;
            }
        } catch (IOException e) {
            throw new RuntimeException("Issue while parsing while type solving: " + srcFile.toAbsolutePath(), e);
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
            Optional<List<CompilationUnit>> cachedValue = parsedDirectories.get(srcDirectory.toAbsolutePath());
            if (cachedValue.isPresent()) {
                return cachedValue.get();
            }

            // If not cached, we need to load it
            List<CompilationUnit> units = new ArrayList<>();
            if (Files.exists(srcDirectory)) {
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
            parsedDirectories.put(srcDirectory.toAbsolutePath(), units);
            return units;
        } catch (IOException e) {
            throw new RuntimeException("Unable to parse directory due to an exception. Directory:" + srcDirectory.toAbsolutePath(), e);
        }

    }

    @Override
    public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
        Optional<SymbolReference<ResolvedReferenceTypeDeclaration>> cachedValue = foundTypes.get(name);
        if (cachedValue.isPresent()) {
            return cachedValue.get();
        }

        // Otherwise load it
        SymbolReference<ResolvedReferenceTypeDeclaration> result = tryToSolveTypeUncached(name);
        foundTypes.put(name, result);
        return result;
    }

    private SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveTypeUncached(String name) {
        String[] nameElements = name.split("\\.");

        for (int i = nameElements.length; i > 0; i--) {
            StringBuilder filePath = new StringBuilder(srcDir.toAbsolutePath().toString());
            for (int j = 0; j < i; j++) {
                filePath.append(File.separator)
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

            String dirToParse = null;
            // As an optimization we first try to look in the canonical position where we expect to find the file
            if (FileUtils.isValidPath(filePath.toString())) {
                Path srcFile = Paths.get(filePath.toString());
                Optional<CompilationUnit> compilationUnit = parse(srcFile);
                if (compilationUnit.isPresent()) {
                    Optional<com.github.javaparser.ast.body.TypeDeclaration<?>> astTypeDeclaration = Navigator
                            .findType(compilationUnit.get(), typeName.toString());
                    if (astTypeDeclaration.isPresent()) {
                        return SymbolReference
                                .solved(JavaParserFacade.get(this).getTypeDeclaration(astTypeDeclaration.get()));
                    }
                }
                dirToParse = srcFile.getParent().normalize().toString();
            } else {
                dirToParse = FileUtils.getParentPath(filePath.toString());
            }

            // If this is not possible we parse all files
            // We try just in the same package, for classes defined in a file not named as the class itself
            if (FileUtils.isValidPath(dirToParse)) {
                List<CompilationUnit> compilationUnits = parseDirectory(Paths.get(dirToParse));
                for (CompilationUnit compilationUnit : compilationUnits) {
                    Optional<com.github.javaparser.ast.body.TypeDeclaration<?>> astTypeDeclaration = Navigator
                            .findType(compilationUnit, typeName.toString());
                    if (astTypeDeclaration.isPresent()) {
                        return SymbolReference
                                .solved(JavaParserFacade.get(this).getTypeDeclaration(astTypeDeclaration.get()));
                    }
                }
            }
        }

        return SymbolReference.unsolved();
    }

}
