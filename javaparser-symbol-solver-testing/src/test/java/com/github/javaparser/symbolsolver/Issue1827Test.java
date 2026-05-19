/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

public class Issue1827Test extends AbstractResolutionTest {

    @Test
    public void solveParametrizedParametersConstructor() {

        String src = """
                public class ParametrizedParametersConstructor {
                    public void foo() {
                        EClass arg = new EClass();
                        ParametrizedClass<String> pc = new ParametrizedClass<>(arg, arg);
                    }
                
                    class EClass implements BaseType<String> {
                    }
                }
                
                class ParametrizedClass<T> {
                    public ParametrizedClass(BaseType<T> arg1, BaseType<T> arg2) {
                    }
                }
                
                interface BaseType<T> {
                }\
                """;

        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(typeSolver);
        StaticJavaParser.getConfiguration().setSymbolResolver(symbolSolver);
        CompilationUnit cu = StaticJavaParser.parse(src);
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ParametrizedParametersConstructor");
        ObjectCreationExpr oce = clazz.findAll(ObjectCreationExpr.class).get(1); // new ParametrizedClass<>(arg, arg)
        assertDoesNotThrow(() -> oce.resolve());
    }
}
