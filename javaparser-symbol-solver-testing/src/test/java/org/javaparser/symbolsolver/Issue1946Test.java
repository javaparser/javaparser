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

import org.javaparser.JavaParser;
import org.javaparser.ParseResult;
import org.javaparser.ParseStart;
import org.javaparser.StringProvider;
import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.expr.FieldAccessExpr;
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import org.javaparser.resolution.declarations.ResolvedValueDeclaration;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue1946Test {


    @Test
    void issueWithInternalEnumConstantReference() {
        String code = "package org.javaparser.symbolsolver.testingclasses; class Foo { void foo() { UtilityClass.method(SomeClass.InnerEnum.CONSTANT); } }";
        JavaParser jp = new JavaParser();
        CombinedTypeSolver typeSolver = new CombinedTypeSolver(new TypeSolver[] {
                new ReflectionTypeSolver(false)
        });
        jp.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        ParseResult<CompilationUnit> pr = jp.parse(ParseStart.COMPILATION_UNIT, new StringProvider(code));
        assertEquals(true, pr.isSuccessful());
        MethodCallExpr methodCallExpr = pr.getResult().get().findFirst(MethodCallExpr.class).get();
        ResolvedMethodDeclaration rmd = methodCallExpr.resolve();
        assertEquals("org.javaparser.symbolsolver.testingclasses.UtilityClass.method(org.javaparser.symbolsolver.testingclasses.SomeClass.InnerEnum)", rmd.getQualifiedSignature());
        FieldAccessExpr fieldAccessExpr = methodCallExpr.findFirst(FieldAccessExpr.class).get();
        ResolvedValueDeclaration rvd = fieldAccessExpr.resolve();
        assertEquals("CONSTANT", rvd.getName());
        assertEquals("org.javaparser.symbolsolver.testingclasses.SomeClass.InnerEnum", rvd.getType().describe());
    }
}
