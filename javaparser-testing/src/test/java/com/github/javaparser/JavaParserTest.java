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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import org.junit.Test;

import java.util.Optional;

import static org.junit.Assert.assertEquals;

public class JavaParserTest {

    @Test
    public void rangeOfAnnotationMemberDeclarationIsCorrect() {
        String code = "@interface AD { String foo(); }";
        CompilationUnit cu = JavaParser.parse(code);
        AnnotationMemberDeclaration memberDeclaration = (AnnotationMemberDeclaration)cu.getAnnotationDeclarationByName("AD").get().getMember(0);
        assertEquals(true, memberDeclaration.getRange().isPresent());
        assertEquals(new Range(new Position(1, 17), new Position(1, 29)), memberDeclaration.getRange().get());
    }

    @Test
    public void rangeOfAnnotationMemberDeclarationWithArrayTypeIsCorrect() {
        String code = "@interface AD { String[] foo(); }";
        CompilationUnit cu = JavaParser.parse(code);
        AnnotationMemberDeclaration memberDeclaration = (AnnotationMemberDeclaration) cu.getAnnotationDeclarationByName("AD").get().getMember(0);
        assertEquals(true, memberDeclaration.getRange().isPresent());
        assertEquals(new Range(new Position(1, 17), new Position(1, 31)), memberDeclaration.getRange().get());
    }

    @Test
    public void rangeOfArrayCreationLevelWithExpressionIsCorrect() {
        String code = "new int[123][456]";
        ArrayCreationExpr expression = (ArrayCreationExpr)JavaParser.parseExpression(code);
        Optional<Range> range;

        range = expression.getLevels().get(0).getRange();
        assertEquals(true, range.isPresent());
        assertEquals(new Range(new Position(1, 8), new Position(1, 12)), range.get());

        range = expression.getLevels().get(1).getRange();
        assertEquals(true, range.isPresent());
        assertEquals(new Range(new Position(1, 13), new Position(1, 17)), range.get());
    }

    @Test
    public void rangeOfArrayCreationLevelWithoutExpressionIsCorrect() {
        String code = "new int[][]";
        ArrayCreationExpr expression = (ArrayCreationExpr)JavaParser.parseExpression(code);
        Optional<Range> range;

        range = expression.getLevels().get(0).getRange();
        assertEquals(true, range.isPresent());
        assertEquals(new Range(new Position(1, 8), new Position(1, 9)), range.get());

        range = expression.getLevels().get(1).getRange();
        assertEquals(true, range.isPresent());
        assertEquals(new Range(new Position(1, 10), new Position(1, 11)), range.get());
    }
}
