/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation.transformations.ast;

import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import com.github.javaparser.utils.Utils;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Transforming ArrayCreationLevel and verifying the LexicalPreservation works as expected.
 */
class ArrayCreationLevelTransformationsTest extends AbstractLexicalPreservingTest {

    protected ArrayCreationLevel consider(String code) {
        considerExpression("new int" + code);
        ArrayCreationExpr arrayCreationExpr = expression.asArrayCreationExpr();
        return arrayCreationExpr.getLevels().get(0);
    }

    // Dimension

    @Test
    void addingDimension() {
        ArrayCreationLevel it = consider("[]");
        it.setDimension(new IntegerLiteralExpr("10"));
        assertTransformedToString("[10]", it);
    }

    @Test
    void removingDimension() {
        ArrayCreationLevel it = consider("[10]");
        it.removeDimension();
        assertTransformedToString("[]", it);
    }

    @Test
    void replacingDimension() {
        ArrayCreationLevel it = consider("[10]");
        it.setDimension(new IntegerLiteralExpr("12"));
        assertTransformedToString("[12]", it);
    }

    // Annotations

    @Test
    void addingAnnotation() {
        ArrayCreationLevel it = consider("[]");
        it.addAnnotation("myAnno");
        assertTransformedToString("@myAnno()"+ Utils.EOL+"[]", it);
    }

    @Test
    void removingAnnotation() {
        ArrayCreationLevel it = consider("@myAnno []");
        it.getAnnotations().remove(0);
        assertTransformedToString("[]", it);
    }

    @Test
    void replacingAnnotation() {
        ArrayCreationLevel it = consider("@myAnno []");
        it.getAnnotations().set(0, new NormalAnnotationExpr(new Name("myOtherAnno"), new NodeList<>()));
        assertTransformedToString("@myOtherAnno() []", it);
    }

}
