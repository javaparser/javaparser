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

package org.javaparser.symbolsolver;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.resolution.MethodUsage;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue228Test extends AbstractResolutionTest{

    @Test
    void testSolvingMethodWitPrimitiveParameterTypeAsUsage() {
        String code = 
                  "class Test { "
                + "  long l = call(1); "
                + "  long call(final long i) { "
                + "    return i; "
                + "  }"
                + "}";
        CompilationUnit cu = parse(code);
        MethodCallExpr methodCall = cu.findAll(MethodCallExpr.class).get(0);
        JavaParserFacade parserFacade = JavaParserFacade.get(new ReflectionTypeSolver());
        MethodUsage solvedCall = parserFacade.solveMethodAsUsage(methodCall);
        assertEquals("long", solvedCall.getParamType(0).describe());
    }
}
