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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledForJreRange;
import org.junit.jupiter.api.condition.JRE;

/**
 * Issue #5263: a direct supertype named in the extends or implements clause (JLS 8.1.4, JLS 8.1.5) is an ancestor
 * of the declaration even when it has a member type whose simple name is the name of the declaration. The expected
 * types are the ones reported by javac 17 for the same sources.
 */
class Issue5263Test {

    private JavaParser javaParser;

    @BeforeEach
    void setup() {
        JavaParserFacade.clearInstances();
        ParserConfiguration configuration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17)
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        javaParser = new JavaParser(configuration);
    }

    private CompilationUnit parse(String code) {
        return javaParser.parse(code).getResult().get();
    }

    private static List<String> ancestors(CompilationUnit cu, String simpleName) {
        return cu
                .findFirst(TypeDeclaration.class, t -> t.getNameAsString().equals(simpleName))
                .get()
                .resolve()
                .getAncestors()
                .stream()
                .map(ResolvedReferenceType::describe)
                .collect(Collectors.toList());
    }

    @Test
    void superclassWithAMemberTypeNamedLikeTheClassIsAnAncestor() {
        CompilationUnit cu = parse("class A extends B {}\nclass B { class A {} }");

        assertEquals(Arrays.asList("B"), ancestors(cu, "A"));
    }

    @Test
    void interfaceWithAMemberTypeNamedLikeTheClassIsAnAncestor() {
        CompilationUnit cu = parse("class C implements I {}\ninterface I { interface C {} }");

        assertEquals(Arrays.asList("java.lang.Object", "I"), ancestors(cu, "C"));
    }

    /** The ancestors of a record include java.lang.Record, which the reflection type solver finds from Java 14. */
    @Test
    @EnabledForJreRange(min = JRE.JAVA_14)
    void interfaceWithAMemberTypeNamedLikeTheRecordIsAnAncestor() {
        CompilationUnit cu = parse("record R() implements Q {}\ninterface Q { interface R {} }");

        assertEquals(Arrays.asList("java.lang.Record", "Q"), ancestors(cu, "R"));
    }

    /** First case of issue #2781: the implemented interface has the name of a member type of the class. */
    @Test
    void memberTypeNamedLikeTheImplementedInterfaceDoesNotLoop() {
        CompilationUnit cu = parse("interface Listener {}\n"
                + "abstract class Container implements Listener {\n"
                + "    private Listener listener;\n"
                + "    protected Listener getContainer() { return listener; }\n"
                + "    protected static class Listener {}\n"
                + "}\n"
                + "class Configuration extends Container {\n"
                + "    Configuration() { getContainer(); }\n"
                + "}");

        assertEquals(Arrays.asList("java.lang.Object", "Listener"), ancestors(cu, "Container"));
        assertEquals(
                "Container.getContainer()",
                cu.findFirst(MethodCallExpr.class).get().resolve().getQualifiedSignature());
    }

    /** Second case of issue #2781: the implemented interface is only declared as a member type of the class. */
    @Test
    void unresolvedInterfaceNamedLikeAMemberTypeDoesNotLoop() {
        CompilationUnit cu = parse("class Controller implements Listener {\n"
                + "    private int selected = 0;\n"
                + "    private Runnable onClick = new Runnable() {\n"
                + "        public void run() { if (selected == 0) { return; } }\n"
                + "    };\n"
                + "    public interface Listener {}\n"
                + "}");

        assertEquals(
                "int",
                cu.findFirst(NameExpr.class, n -> n.getNameAsString().equals("selected"))
                        .get()
                        .calculateResolvedType()
                        .describe());
    }
}
