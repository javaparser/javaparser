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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.Optional;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class Issue3710Test {
    @Test
    void resolve_method_used_as_scope_for_inner_class_object_creation() {
        String sourceCode = "class Example {\n"
                + "  void test() {\n"
                + "    Outer.make().new Inner();\n"
                + "  }\n"
                + "}\n"
                + "class Outer {\n"
                + "  class Inner {}\n"
                + "  static Outer make() { return new Outer(); }\n"
                + "}";
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver(false));
        SymbolResolver resolver = new JavaSymbolSolver(combinedTypeSolver);
        ParserConfiguration config = new ParserConfiguration().setSymbolResolver(resolver);
        JavaParser parser = new JavaParser(config);
        CompilationUnit compilationUnit = parser.parse(sourceCode).getResult().get();
        Optional<MethodCallExpr> methodCall = compilationUnit.findFirst(MethodCallExpr.class);

        ResolvedMethodDeclaration resolvedMethod = methodCall.get().resolve();

        Assertions.assertEquals("Outer.make()", resolvedMethod.getQualifiedSignature());
    }

    @Test
    void resolve_chained_inner_class_object_creation() {
        String sourceCode = "class Example {\n"
                + "  void test() {\n"
                + "    Outer.make().new Middle().new Inner();\n"
                + "  }\n"
                + "}\n"
                + "class Outer {\n"
                + "  class Middle { class Inner {} }\n"
                + "  static Outer make() { return new Outer(); }\n"
                + "}";
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver(false));
        SymbolResolver resolver = new JavaSymbolSolver(combinedTypeSolver);
        ParserConfiguration config = new ParserConfiguration().setSymbolResolver(resolver);
        JavaParser parser = new JavaParser(config);
        CompilationUnit compilationUnit = parser.parse(sourceCode).getResult().get();
        Optional<ObjectCreationExpr> constructorCall = compilationUnit.findFirst(ObjectCreationExpr.class);

        ObjectCreationExpr innerConstructor = constructorCall.get();
        ObjectCreationExpr middleConstructor = innerConstructor.getScope().get().asObjectCreationExpr();
        MethodCallExpr outerFactory = middleConstructor.getScope().get().asMethodCallExpr();

        Assertions.assertEquals(
                "Outer.Middle.Inner.Inner()", innerConstructor.resolve().getQualifiedSignature());
        Assertions.assertEquals(
                "Outer.Middle.Middle()", middleConstructor.resolve().getQualifiedSignature());
        Assertions.assertEquals("Outer.make()", outerFactory.resolve().getQualifiedSignature());
    }

    @Test
    void resolve_inner_class_object_creation_starting_with_constructor() {
        String sourceCode = "class Example {\n"
                + "  void test() {\n"
                + "    new Outer().new Middle().new Inner();\n"
                + "  }\n"
                + "}\n"
                + "class Outer {\n"
                + "  class Middle { class Inner {} }\n"
                + "}";
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver(false));
        SymbolResolver resolver = new JavaSymbolSolver(combinedTypeSolver);
        ParserConfiguration config = new ParserConfiguration().setSymbolResolver(resolver);
        JavaParser parser = new JavaParser(config);
        CompilationUnit compilationUnit = parser.parse(sourceCode).getResult().get();
        Optional<ObjectCreationExpr> constructorCall = compilationUnit.findFirst(ObjectCreationExpr.class);

        ObjectCreationExpr innerConstructor = constructorCall.get();
        ObjectCreationExpr middleConstructor = innerConstructor.getScope().get().asObjectCreationExpr();
        ObjectCreationExpr outerConstructor = middleConstructor.getScope().get().asObjectCreationExpr();

        Assertions.assertEquals(
                "Outer.Middle.Inner.Inner()", innerConstructor.resolve().getQualifiedSignature());
        Assertions.assertEquals(
                "Outer.Middle.Middle()", middleConstructor.resolve().getQualifiedSignature());
        Assertions.assertEquals("Outer.Outer()", outerConstructor.resolve().getQualifiedSignature());
    }
}
