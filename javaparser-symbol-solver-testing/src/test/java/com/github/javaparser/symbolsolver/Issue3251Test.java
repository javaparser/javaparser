/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.*;

public class Issue3251Test {

    @BeforeEach
    void setup() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        JavaSymbolSolver symbolResolver = new JavaSymbolSolver(typeResolver);
        StaticJavaParser.getParserConfiguration().setSymbolResolver(symbolResolver);
    }

    @Test
    void resolveNameAsType() {
        String code = "class A { int a = Integer.MAX_VALUE; }";
        CompilationUnit cu = parse(code);
        NameExpr integerTypeNameExpr = cu.findFirst(NameExpr.class).get();

        ResolvedDeclaration resolved = integerTypeNameExpr.resolve();

        assertTrue(resolved.isType());
        assertInstanceOf(ResolvedTypeDeclaration.class, resolved);
        assertEquals("java.lang.Integer", ((ResolvedTypeDeclaration) resolved).getQualifiedName());
    }
}
