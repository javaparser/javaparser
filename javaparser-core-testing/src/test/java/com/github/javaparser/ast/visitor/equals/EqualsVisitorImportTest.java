/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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
package com.github.javaparser.ast.visitor.equals;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.comments.LineComment;
import org.junit.jupiter.api.Test;

public class EqualsVisitorImportTest extends EqualsVisitorTest {
    private static final String IMPORT = "import static java.util.Collections.*;";

    @Test
    void equals_sameImport_true() {
        parseAndClone(IMPORT);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentName_false() {
        parseAndClone(IMPORT);
        ImportDeclaration imp = nodeRight.getImport(0);
        imp.setName("java.util.List");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentIsAsterisk_false() {
        parseAndClone(IMPORT);
        ImportDeclaration imp = nodeRight.getImport(0);
        imp.setAsterisk(false);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentIsStatic_false() {
        parseAndClone(IMPORT);
        ImportDeclaration imp = nodeRight.getImport(0);
        imp.setStatic(false);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentIsModule_false() {
        parseAndClone(IMPORT);
        ImportDeclaration imp = nodeRight.getImport(0);
        imp.setModule(true);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentComment_false() {
        parseAndClone(IMPORT);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        ImportDeclaration imp = nodeRight.getImport(0);
        imp.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
