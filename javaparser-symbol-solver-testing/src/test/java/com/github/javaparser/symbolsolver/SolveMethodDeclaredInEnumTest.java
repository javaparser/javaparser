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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StringProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

class SolveMethodDeclaredInEnumTest extends AbstractSymbolResolutionTest {

    @Test
    void methodDeclaredInEnum_enumFromJar() throws IOException {
        String code = "public class A { public void callEnum() { MyEnum.CONST.method(); }}";
        Path jarPath = adaptPath("src/test/resources/solveMethodDeclaredInEnum/MyEnum.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JarTypeSolver(jarPath), new ReflectionTypeSolver());

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(
                new JavaSymbolSolver(typeSolver));
        JavaParser javaParser = new JavaParser(parserConfiguration);

        CompilationUnit cu = javaParser.parse(ParseStart.COMPILATION_UNIT, new StringProvider(code)).getResult().get();

        MethodCallExpr call = cu.findFirst(MethodCallExpr.class).orElse(null);
        ResolvedMethodDeclaration resolvedCall = call.resolve();

        assertNotNull(resolvedCall);
        assertEquals("MyEnum.method()", resolvedCall.getQualifiedSignature());
    }

}
