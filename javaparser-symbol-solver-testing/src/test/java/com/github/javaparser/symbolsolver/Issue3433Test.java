/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedVoidType;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserParameterDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.ExtractingVisitors;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.symbolsolver.utils.TestUtils.parseFile;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class Issue3433Test {

    @Test
    void testParseRecurssiveGenerics() {
        CompilationUnit compilationUnit = parseFile("/Issue3433.java.txt");

        JavaSymbolSolver javaSymbolSolver = new JavaSymbolSolver(new ReflectionTypeSolver());
        javaSymbolSolver.inject(compilationUnit);

        List<MethodCallExpr> methodCallExprs = ExtractingVisitors.extractMethodCallExprs(compilationUnit);
        assertEquals(1, methodCallExprs.size());

        JavaParserMethodDeclaration methodDeclaration = resolveMethod(methodCallExprs, 0);
        assertEquals("method1", methodDeclaration.getName());
        assertEquals(ResolvedVoidType.INSTANCE, methodDeclaration.getReturnType());

        assertEquals(1, methodDeclaration.getNumberOfParams());
        assertEquals("Collection<T> options", paramDeclToString(methodDeclaration.getParam(0)));

        List<ResolvedTypeParameterDeclaration> typeParameters = methodDeclaration.getTypeParameters();
        assertEquals(2, typeParameters.size());
        assertEquals("E", typeParameterToString(typeParameters.get(0)));
        assertEquals("T extends Collection<? extends E>", typeParameterToString(typeParameters.get(1)));
    }

    private JavaParserMethodDeclaration resolveMethod(List<MethodCallExpr> methodCallExprs, int i) {
        MethodCallExpr methodCallExpr = methodCallExprs.get(i);
        ResolvedMethodDeclaration resolve = methodCallExpr.resolve();
        assertTrue(resolve instanceof JavaParserMethodDeclaration);
        return (JavaParserMethodDeclaration) resolve;
    }

    private String paramDeclToString(ResolvedParameterDeclaration resolvedParameterDeclaration) {
        assertTrue(resolvedParameterDeclaration instanceof JavaParserParameterDeclaration);
        JavaParserParameterDeclaration decl = (JavaParserParameterDeclaration) resolvedParameterDeclaration;
        Parameter wrappedNode = decl.getWrappedNode();
        return wrappedNode.toString();
    }

    private String typeParameterToString(ResolvedTypeParameterDeclaration typeParameter) {
        assertTrue(typeParameter instanceof JavaParserTypeParameter);
        JavaParserTypeParameter param = (JavaParserTypeParameter) typeParameter;
        TypeParameter wrappedNode = param.getWrappedNode();
        return wrappedNode.toString();
    }

}