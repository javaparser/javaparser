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

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import java.util.List;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

public class Issue3037Test extends AbstractResolutionTest {

    @Test
    void resolvingOverloadedMethodWithLambdaShouldUseParameterCountToDisambiguate() {
        // File.listFiles(FileFilter) takes a 1-parameter functional interface
        // File.listFiles(FilenameFilter) takes a 2-parameter functional interface
        // A 2-parameter lambda should resolve to the FilenameFilter overload
        String code = "import java.io.File;\n"
                + "class A {\n"
                + "    void test() {\n"
                + "        File directory = new File(\".\");\n"
                + "        File[] files = directory.listFiles((dir, name) -> name.endsWith(\".txt\"));\n"
                + "    }\n"
                + "}";
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = StaticJavaParser.parse(code);
        MethodCallExpr mce = cu.findFirst(MethodCallExpr.class).get();
        ResolvedMethodDeclaration resolved = mce.resolve();
        assertEquals("listFiles", resolved.getName());
        assertEquals(1, resolved.getNumberOfParams());
        assertEquals(
                "java.io.FilenameFilter",
                resolved.getParam(0).getType().asReferenceType().getQualifiedName());
    }

    @Test
    void resolvingOverloadedMethodWithSingleParamLambdaShouldResolveToFileFilter() {
        // A 1-parameter lambda should resolve to the FileFilter overload
        String code = "import java.io.File;\n"
                + "class A {\n"
                + "    void test() {\n"
                + "        File directory = new File(\".\");\n"
                + "        File[] files = directory.listFiles(f -> f.isDirectory());\n"
                + "    }\n"
                + "}";
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = StaticJavaParser.parse(code);
        MethodCallExpr mce = cu.findFirst(MethodCallExpr.class).get();
        ResolvedMethodDeclaration resolved = mce.resolve();
        assertEquals("listFiles", resolved.getName());
        assertEquals(1, resolved.getNumberOfParams());
        assertEquals(
                "java.io.FileFilter",
                resolved.getParam(0).getType().asReferenceType().getQualifiedName());
    }

    @Test
    void resolvingMethodCallInsideLambdaOnReflectionResolvedType() {
        // Reproduces AnalyseJavaSymbolSolver060Test failure:
        // s.getQualifiedName().equals(Object.class.getCanonicalName()) inside a lambda
        // must resolve equals to java.lang.String.equals(java.lang.Object)
        String code = "import java.util.*;\n"
                + "class A {\n"
                + "    void test() {\n"
                + "        List<String> list = new ArrayList<>();\n"
                + "        list.removeIf(s -> s.equals(Object.class.getCanonicalName()));\n"
                + "    }\n"
                + "}";
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = StaticJavaParser.parse(code);
        // Find the equals() call (second MethodCallExpr, after removeIf)
        List<MethodCallExpr> calls = cu.findAll(MethodCallExpr.class);
        MethodCallExpr equalsCall = calls.stream()
                .filter(m -> m.getNameAsString().equals("equals"))
                .findFirst().get();
        ResolvedMethodDeclaration resolved = equalsCall.resolve();
        assertEquals("equals", resolved.getName());
        assertEquals("java.lang.Object",
                resolved.getParam(0).getType().asReferenceType().getQualifiedName());
    }
}
