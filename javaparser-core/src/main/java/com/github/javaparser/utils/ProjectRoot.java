/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.ParserConfiguration;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The structure of a Java project directory.
 * It was originally created specifically to quickly configure the symbol solver.
 * You can use it as a general container for project information.
 * <p>A project has a root directory, and it has zero or more directories that contain source code.
 * <p>To create a ProjectRoot use a CollectionStrategy, or instantiate ProjectRoot yourself.
 */
public class ProjectRoot {

    private final Path root;

    private final Map<Path, SourceRoot> cache = new ConcurrentHashMap<>();

    private final ParserConfiguration parserConfiguration;

    public ProjectRoot(Path root) {
        this(root, new ParserConfiguration());
    }

    public ProjectRoot(Path root, ParserConfiguration parserConfiguration) {
        this.root = root;
        this.parserConfiguration = parserConfiguration;
    }

    public Optional<SourceRoot> getSourceRoot(Path sourceRoot) {
        return Optional.ofNullable(cache.get(sourceRoot));
    }

    public List<SourceRoot> getSourceRoots() {
        return new ArrayList<>(cache.values());
    }

    public void addSourceRoot(Path path) {
        cache.put(path, new SourceRoot(path).setParserConfiguration(parserConfiguration));
    }

    public Path getRoot() {
        return root;
    }

    @Override
    public String toString() {
        return "ProjectRoot at " + root + " with " + cache.values().toString();
    }
}
