/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametersMap;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class Issue2951Test {
    @Test
    public void testResolveListOfByteArray() throws IOException {
        ParserConfiguration config = new ParserConfiguration();
        CombinedTypeSolver typeResolver = new CombinedTypeSolver(new ReflectionTypeSolver(false));
        typeResolver.add(new JarTypeSolver("src/test/resources/issue2951/a.jar"));
        config.setSymbolResolver(new JavaSymbolSolver(typeResolver));
        StaticJavaParser.setConfiguration(config);

        ResolvedReferenceTypeDeclaration clazzA = typeResolver.solveType("foo.A");
        Optional<ResolvedMethodDeclaration> optionalMethod = clazzA.getDeclaredMethods().stream().filter(m -> m.getName().equals("get")).findFirst();
        assertTrue(optionalMethod.isPresent());

        ResolvedMethodDeclaration method = optionalMethod.get();
        ResolvedType paramType = method.getParam(0).getType();
        assertTrue(paramType.isReferenceType());
        ResolvedReferenceType referenceType = paramType.asReferenceType();
        ResolvedTypeParametersMap typeParametersMap = referenceType.typeParametersMap();
        ResolvedType type = typeParametersMap.getTypes().get(0);
        assertTrue(type instanceof ResolvedArrayType);
    }

    @Test
    public void testIssue2951() throws IOException {
        ParserConfiguration config = new ParserConfiguration();
        CombinedTypeSolver typeResolver = new CombinedTypeSolver(new ReflectionTypeSolver(false));
        typeResolver.add(new JarTypeSolver("src/test/resources/issue2951/a.jar"));
        config.setSymbolResolver(new JavaSymbolSolver(typeResolver));
        StaticJavaParser.setConfiguration(config);

        String code = "package foo;\n"
                + "import java.util.List;\n"
                + "import foo.A;\n"
                + "public class Test {\n"
                + "    public void foo() {\n"
                + "        List<byte[]> keys = new ArrayList<>();\n"
                + "        A a = new A();\n"
                + "        a.get(keys);\n"
                + "    }\n"
                + "}";
        CompilationUnit cu = StaticJavaParser.parse(code);

        for (TypeDeclaration<?> type : cu.getTypes()) {
            type.ifClassOrInterfaceDeclaration(classDecl -> {
                for (MethodDeclaration method : classDecl.getMethods()) {
                    method.getBody().ifPresent(body -> {
                        for (Statement stmt : body.getStatements()) {
                            for (MethodCallExpr methodCallExpr : stmt.findAll(MethodCallExpr.class)) {
                                ResolvedMethodDeclaration resolvedMethodCall = methodCallExpr.resolve();
                                String methodSig = resolvedMethodCall.getQualifiedSignature();
                                assertEquals("foo.A.get(java.util.List<byte[]>)", methodSig);
                            }
                        }
                    });
                }
            });
        }
    }
}
