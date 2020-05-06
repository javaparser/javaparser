/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

package com.github.javaparser.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.util.Optional;

/**
 * A strategy for discovering the structure of a project.
 * Implementations could read a pom.xml, a Gradle build file, a makefile...
 */
public interface CollectionStrategy {

    ParserConfiguration getParserConfiguration();

    ProjectRoot collect(Path path);

    default Optional<Path> getRoot(Path file) {
        try {
            final JavaParser javaParser = new JavaParser(getParserConfiguration());
            final ParseResult<CompilationUnit> parseResult = javaParser.parse(file);

            if (parseResult.isSuccessful()) {
                if (parseResult.getProblems().isEmpty()) {
                    if (parseResult.getResult().isPresent()) {
                        final CompilationUnit compilationUnit = parseResult.getResult().get();
                        final Optional<CompilationUnit.Storage> storage = compilationUnit.getStorage();
                        if (storage.isPresent()) {
                            final Optional<Path> sourceRootPath = storage.map(CompilationUnit.Storage::getSourceRoot);
                            return sourceRootPath;
                        } else {
                            Log.info("Storage information not present -- an issue with providing a string rather than file reference?");
                        }
                    } else {
                        Log.info("Parse result not present");
                    }
                } else {
                    Log.info("There were (%d) problems parsing file: %s", () -> parseResult.getProblems().size(), () -> parseResult.getProblems());
                }
            } else {
                Log.info("Parsing was not successful.");
                Log.info("There were (%d) problems parsing file: %s", () -> parseResult.getProblems().size(), () -> parseResult.getProblems());
            }
        } catch (ParseProblemException e) {
            Log.info("Problem parsing file %s", () -> file);
        } catch (RuntimeException e) {
            Log.info("Could not parse file %s", () -> file);
        } catch (IOException e) {
            Log.info("Could not read file %s", () -> file);
        }
        return Optional.empty();
    }

    default PathMatcher getPathMatcher(String pattern) {
        return FileSystems.getDefault().getPathMatcher(pattern);
    }
}
