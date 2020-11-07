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

package com.github.javaparser.symbolsolver.utils;

import static java.nio.file.FileVisitResult.CONTINUE;
import static java.nio.file.FileVisitResult.SKIP_SUBTREE;

import java.io.IOException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.CollectionStrategy;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.ProjectRoot;

/**
 * {@link CollectionStrategy} which collects all SourceRoots and initialises the TypeSolver and
 * returns the SourceRoots configured with the TypeSolver in a ProjectRoot object.
 */
public class SymbolSolverCollectionStrategy implements CollectionStrategy {

    private final ParserConfiguration parserConfiguration;
    private final CombinedTypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(false));

    public SymbolSolverCollectionStrategy() {
        this(new ParserConfiguration());
    }

    public SymbolSolverCollectionStrategy(ParserConfiguration parserConfiguration) {
        // Allow the symbol resolver to be set via the given parser configuration
        this.parserConfiguration = parserConfiguration;
        if (!parserConfiguration.getSymbolResolver().isPresent()) {
            this.parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        }
    }

    @Override
    public ParserConfiguration getParserConfiguration() {
        return parserConfiguration;
    }

    @Override
    public ProjectRoot collect(Path path) {
        ProjectRoot projectRoot = new ProjectRoot(path, parserConfiguration);
        try {
            Files.walkFileTree(path, new SimpleFileVisitor<Path>() {
                private Path current_root;
                private final PathMatcher javaMatcher = getPathMatcher("glob:**.java");
                private final PathMatcher jarMatcher = getPathMatcher("glob:**.jar");

                @Override
                public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
                    if (javaMatcher.matches(file)) {
                        if (current_root == null || !file.startsWith(current_root)) {
                            current_root = getRoot(file).orElse(null);
                        }
                    } else if (jarMatcher.matches(file)) {
                        typeSolver.add(new JarTypeSolver(file.toString()));
                    }
                    return CONTINUE;
                }

                @Override
                public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
                    if (Files.isHidden(dir)) {
                        return SKIP_SUBTREE;
                    }
                    return CONTINUE;
                }

                @Override
                public FileVisitResult postVisitDirectory(Path dir, IOException e) throws IOException {
                    if (current_root != null && Files.isSameFile(dir, current_root)) {
                        projectRoot.addSourceRoot(dir);
                        typeSolver.add(new JavaParserTypeSolver(current_root.toFile(), parserConfiguration));
                        current_root = null;
                    }
                    return CONTINUE;
                }
            });
        } catch (IOException e) {
            Log.error(e, "Unable to walk %s", () -> path);
        }
        return projectRoot;
    }
}
