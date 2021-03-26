/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.expr.*;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class Issue343Test extends AbstractResolutionTest{

    private TypeSolver typeResolver;
    private JavaParserFacade javaParserFacade;

    private ResolvedType getExpressionType(TypeSolver typeSolver, Expression expression) {
        return JavaParserFacade.get(typeSolver).getType(expression);
    }

    @BeforeEach
    void setup() {
        typeResolver = new ReflectionTypeSolver();
        javaParserFacade = JavaParserFacade.get(typeResolver);
    }

    @Test
    void resolveStringLiteralOutsideAST() {
        assertEquals(javaParserFacade.classToResolvedType(String.class), getExpressionType(typeResolver, new StringLiteralExpr("")));
    }

    @Test
    void resolveIntegerLiteralOutsideAST() {
        assertEquals(javaParserFacade.classToResolvedType(int.class), getExpressionType(typeResolver, new IntegerLiteralExpr(2)));
    }

    @Test
    void toResolveDoubleWeNeedTheAST() {
        assertThrows(IllegalStateException.class, () -> getExpressionType(typeResolver, parseExpression("new Double[]{2.0d, 3.0d}[1]")));
    }


    @Test
    void toResolveFloatWeNeedTheAST() {
        assertThrows(IllegalStateException.class, () -> getExpressionType(typeResolver, parseExpression("new Float[]{2.0d, 3.0d}")));
    }

    @Test
    void resolveMethodCallOnStringLiteralOutsideAST() {
        assertEquals(javaParserFacade.classToResolvedType(int.class), getExpressionType(typeResolver, new MethodCallExpr(new StringLiteralExpr("hello"), "length")));
    }

    @Test
    void resolveLocaleOutsideAST() {
        assertThrows(IllegalStateException.class, () -> getExpressionType(typeResolver, new FieldAccessExpr(new NameExpr("Locale"), "US")));
    }
}
