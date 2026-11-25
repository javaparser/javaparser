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
 * Issue #5265: a local class or record (JLS 14.3), and a class nested in a local class, has no fully qualified name
 * (JLS 6.7), but it still has the direct supertypes named in its extends and implements clauses (JLS 8.1.4,
 * JLS 8.1.5). The expected types are the ones reported by javac 17 for the same sources.
 */
class Issue5265Test {

    private static final String LOCAL_TYPES = "interface I {}\n"
            + "class Top {\n"
            + "    void m() {\n"
            + "        class B { void f() {} }\n"
            + "        class A extends B implements I {}\n"
            + "        class C implements I { class N extends B {} }\n"
            + "        record R() implements I {}\n"
            + "        new A().f();\n"
            + "    }\n"
            + "}";

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
                .map(ancestor -> ancestor.getTypeDeclaration().get().getName())
                .collect(Collectors.toList());
    }

    @Test
    void localClassHasTheSupertypesOfItsClauses() {
        CompilationUnit cu = parse(LOCAL_TYPES);

        assertEquals(Arrays.asList("B", "I"), ancestors(cu, "A"));
        assertEquals(Arrays.asList("Object", "I"), ancestors(cu, "C"));
    }

    @Test
    void classNestedInALocalClassHasTheSupertypeOfItsClause() {
        CompilationUnit cu = parse(LOCAL_TYPES);

        assertEquals(Arrays.asList("B"), ancestors(cu, "N"));
    }

    /** The ancestors of a record include java.lang.Record, which the reflection type solver finds from Java 14. */
    @Test
    @EnabledForJreRange(min = JRE.JAVA_14)
    void localRecordHasTheSupertypesOfItsClause() {
        CompilationUnit cu = parse(LOCAL_TYPES);

        assertEquals(Arrays.asList("Record", "I"), ancestors(cu, "R"));
    }

    @Test
    void methodInheritedByALocalClassIsResolved() {
        CompilationUnit cu = parse(LOCAL_TYPES);

        assertEquals("f", cu.findFirst(MethodCallExpr.class).get().resolve().getName());
    }
}
