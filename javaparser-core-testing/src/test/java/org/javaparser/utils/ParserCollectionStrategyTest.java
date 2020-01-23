/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

import org.junit.jupiter.api.Test;

import java.nio.file.Path;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;


class ParserCollectionStrategyTest {

    private final Path root = CodeGenerationUtils.mavenModuleRoot(ParserCollectionStrategyTest.class).resolve("").getParent();
    private final ProjectRoot projectRoot = new ParserCollectionStrategy().collect(root);

    @Test
    void getSourceRoots() {
        assertFalse(projectRoot.getSourceRoots().size() == 0);
        assertNotEquals(Optional.empty(), projectRoot.getSourceRoot(root.resolve("javaparser-core/src/main/java")));
        assertNotEquals(Optional.empty(), projectRoot.getSourceRoot(root.resolve
                ("javaparser-core-generators/src/main/java")));
        assertNotEquals(Optional.empty(), projectRoot.getSourceRoot(root.resolve
                ("javaparser-core-metamodel-generator/src/main/java")));
        assertNotEquals(Optional.empty(), projectRoot.getSourceRoot(root.resolve
                ("javaparser-symbol-solver-core/src/main/java")));
        assertNotEquals(Optional.empty(), projectRoot.getSourceRoot(root.resolve
                ("javaparser-symbol-solver-logic/src/main/java")));
        assertNotEquals(Optional.empty(), projectRoot.getSourceRoot(root.resolve
                ("javaparser-symbol-solver-model/src/main/java")));
    }
}
