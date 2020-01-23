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

package org.javaparser.symbolsolver.resolution;

import org.javaparser.ParserConfiguration;
import org.javaparser.StaticJavaParser;
import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.resolution.MethodUsage;
import org.javaparser.symbolsolver.core.resolution.Context;
import org.javaparser.symbolsolver.javaparser.Navigator;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.javaparsermodel.contexts.CompilationUnitContext;
import org.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.javaparser.utils.Log;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class MethodsResolutionWithJavassistTest extends AbstractResolutionTest {

    @AfterEach
    void resetConfiguration() {
        StaticJavaParser.setConfiguration(new ParserConfiguration());
        Log.setAdapter(new Log.SilentAdapter());
    }

    @Test
    public void testOverloadedMethods() throws Exception {
        CompilationUnit cu = parseSample("OverloadedMethodCall");

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/javaparser-core-3.0.0-alpha.2.jar")));
        typeSolver.add(new ReflectionTypeSolver());

        Context context = new CompilationUnitContext(cu, typeSolver);
        ClassOrInterfaceDeclaration classA = Navigator.demandClass(cu, "OverloadedMethodCall");
        MethodDeclaration method = Navigator.demandMethod(classA, "foo");

        List<MethodCallExpr> calls = method.findAll(MethodCallExpr.class, n -> n.getNameAsString().equals("accept"));
        assertEquals(2, calls.size());

        // node.accept((GenericVisitor) null, null);
        MethodUsage methodUsage1 = JavaParserFacade.get(typeSolver).solveMethodAsUsage(calls.get(0));
        assertEquals("com.github.javaparser.ast.visitor.GenericVisitor<R, A>", methodUsage1.getParamType(0).describe());

        // node.accept((VoidVisitor) null, null);
        MethodUsage methodUsage2 = JavaParserFacade.get(typeSolver).solveMethodAsUsage(calls.get(1));
        assertEquals("com.github.javaparser.ast.visitor.VoidVisitor<A>", methodUsage2.getParamType(0).describe());
    }
}
