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

package org.javaparser.utils;

import org.javaparser.ParseProblemException;
import org.javaparser.ast.CompilationUnit;

import java.io.FileNotFoundException;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.util.Optional;

import static org.javaparser.StaticJavaParser.parse;

/**
 * A strategy for discovering the structure of a project.
 * Implementations could read a pom.xml, a Gradle build file, a makefile...
 */
public interface CollectionStrategy {

    ProjectRoot collect(Path path);

    default Optional<Path> getRoot(Path file) throws FileNotFoundException {
        try {
            return parse(file.toFile()).getStorage()
                    .map(CompilationUnit.Storage::getSourceRoot);
        } catch (ParseProblemException e) {
            Log.info("Problem parsing file %s", () -> file);
        } catch (RuntimeException e) {
            Log.info("Could not parse file %s", () -> file);
        }
        return Optional.empty();
    }

    default PathMatcher getPathMatcher(String pattern) {
        return FileSystems.getDefault().getPathMatcher(pattern);
    }
}
