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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.expr.*;
import com.github.javaparser.resolution.Solver;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.*;

/**
 * Note this issue number refers to the archived `javasymbolsolver` repository,
 * whose issues prior to it being integrated into JavaParser itself are numbered separately:
 *
 * https://github.com/javaparser/javasymbolsolver/issues/343
 */
class Issue343Test extends AbstractResolutionTest {

    private TypeSolver typeResolver;
    private Solver symbolSolver;

    private ResolvedType getExpressionType(TypeSolver typeSolver, Expression expression) {
        return JavaParserFacade.get(typeSolver).getType(expression);
    }

    @BeforeEach
    void setup() {
        typeResolver = new ReflectionTypeSolver();
        symbolSolver = new SymbolSolver(typeResolver);
    }

    @Test
    void resolveStringLiteralOutsideAST() {
        assertTrue(symbolSolver.classToResolvedType(String.class).equals(getExpressionType(typeResolver, new StringLiteralExpr(""))));
    }

    @Test
    void resolveIntegerLiteralOutsideAST() {
        assertEquals(symbolSolver.classToResolvedType(int.class), getExpressionType(typeResolver, new IntegerLiteralExpr(2)));
    }

    @Test
    void toResolveDoubleWeNeedTheAST() {
        assertThrows(UnsolvedSymbolException.class, () -> getExpressionType(typeResolver, parseExpression("new Double[]{2.0d, 3.0d}[1]")));
    }


    @Test
    void toResolveFloatWeNeedTheAST() {
        assertThrows(UnsolvedSymbolException.class, () -> getExpressionType(typeResolver, parseExpression("new Float[]{2.0d, 3.0d}[1]")));
    }

    @Test
    void resolveMethodCallOnStringLiteralOutsideAST() {
    	assertTrue(symbolSolver.classToResolvedType(int.class).equals(getExpressionType(typeResolver, new MethodCallExpr(new StringLiteralExpr("hello"), "length"))));
    }

    @Test
    void resolveLocaleOutsideAST() {
        assertThrows(IllegalStateException.class, () -> getExpressionType(typeResolver, new FieldAccessExpr(new NameExpr("Locale"), "US")));
    }
}
