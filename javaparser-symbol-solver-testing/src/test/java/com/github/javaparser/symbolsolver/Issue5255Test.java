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
import com.github.javaparser.ast.nodeTypes.NodeWithExtends;
import com.github.javaparser.ast.nodeTypes.NodeWithImplements;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledForJreRange;
import org.junit.jupiter.api.condition.JRE;

/**
 * Issue #5255: the types of the {@code extends} and {@code implements} clauses, and their type arguments, must not
 * be resolved against the member types of the declaration (JLS 6.3), whatever the kind of the declaration. The
 * expected types are the ones reported by javac 17 for the same sources.
 */
class Issue5255Test {

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

    private static TypeDeclaration<?> declaration(CompilationUnit cu, String simpleName) {
        return cu.findFirst(TypeDeclaration.class, t -> t.getNameAsString().equals(simpleName))
                .get();
    }

    /** The types of the extends and implements clauses of the declaration, resolved one by one. */
    private static List<String> clauseTypes(CompilationUnit cu, String simpleName) {
        TypeDeclaration<?> declaration = declaration(cu, simpleName);
        List<ClassOrInterfaceType> clause = new ArrayList<>();
        if (declaration instanceof NodeWithExtends) {
            clause.addAll(((NodeWithExtends<?>) declaration).getExtendedTypes());
        }
        if (declaration instanceof NodeWithImplements) {
            clause.addAll(((NodeWithImplements<?>) declaration).getImplementedTypes());
        }
        return clause.stream().map(type -> type.resolve().describe()).collect(Collectors.toList());
    }

    private static List<String> ancestors(CompilationUnit cu, String simpleName) {
        return declaration(cu, simpleName).resolve().getAncestors().stream()
                .map(ResolvedReferenceType::describe)
                .collect(Collectors.toList());
    }

    private static final String MEMBER_WITH_THE_SAME_NAME = "interface I {}\n"
            + "interface G<T> {}\n"
            + "class C implements I, G<I> { interface I {} }\n"
            + "interface P extends I, G<I> { interface I {} }\n"
            + "enum O implements I, G<I> { A; interface I {} }\n"
            + "record R() implements I, G<I> { interface I {} }";

    @Test
    void clauseOfAnEnumIsResolvedFromTheEnclosingScope() {
        CompilationUnit cu = parse(MEMBER_WITH_THE_SAME_NAME);

        assertEquals(Arrays.asList("I", "G<I>"), clauseTypes(cu, "O"));
        assertEquals(Arrays.asList("java.lang.Enum<O>", "I", "G<I>"), ancestors(cu, "O"));
    }

    @Test
    void clauseOfARecordIsResolvedFromTheEnclosingScope() {
        CompilationUnit cu = parse(MEMBER_WITH_THE_SAME_NAME);

        assertEquals(Arrays.asList("I", "G<I>"), clauseTypes(cu, "R"));
    }

    /** The ancestors of a record include java.lang.Record, which the reflection type solver finds from Java 14. */
    @Test
    @EnabledForJreRange(min = JRE.JAVA_14)
    void ancestorsOfARecordAreResolvedFromTheEnclosingScope() {
        CompilationUnit cu = parse(MEMBER_WITH_THE_SAME_NAME);

        assertEquals(Arrays.asList("java.lang.Record", "I", "G<I>"), ancestors(cu, "R"));
    }

    @Test
    void clauseOfAClassOrAnInterfaceIsStillResolvedFromTheEnclosingScope() {
        CompilationUnit cu = parse(MEMBER_WITH_THE_SAME_NAME);

        assertEquals(Arrays.asList("I", "G<I>"), clauseTypes(cu, "C"));
        assertEquals(Arrays.asList("java.lang.Object", "I", "G<I>"), ancestors(cu, "C"));
        assertEquals(Arrays.asList("I", "G<I>"), clauseTypes(cu, "P"));
        assertEquals(Arrays.asList("I", "G<I>"), ancestors(cu, "P"));
    }

    @Test
    void typeParametersOfTheRecordAreStillVisibleInItsClause() {
        CompilationUnit cu = parse("interface G<T> {}\nrecord R<T>() implements G<T> {}");

        assertEquals(Arrays.asList("G<T>"), clauseTypes(cu, "R"));
    }

    @Test
    @EnabledForJreRange(min = JRE.JAVA_14)
    void typeParametersOfTheRecordAreStillVisibleInItsAncestors() {
        CompilationUnit cu = parse("interface G<T> {}\nrecord R<T>() implements G<T> {}");

        assertEquals(Arrays.asList("java.lang.Record", "G<T>"), ancestors(cu, "R"));
    }

    @Test
    void typesDeclaredInTheEnclosingTypeAreStillResolved() {
        CompilationUnit cu =
                parse("class Outer { interface X {} enum E implements X { A } record R() implements X {} }");

        assertEquals(Arrays.asList("Outer.X"), clauseTypes(cu, "E"));
        assertEquals(Arrays.asList("Outer.X"), clauseTypes(cu, "R"));
    }

    @Test
    void typesDeclaredInTheEnclosingBlockAreStillResolved() {
        CompilationUnit cu =
                parse("class Top { void m() { interface X {} enum E implements X { A } record R() implements X {} } }");
        String x = declaration(cu, "X").resolve().getQualifiedName();

        assertEquals(Arrays.asList(x), clauseTypes(cu, "E"));
        assertEquals(Arrays.asList(x), clauseTypes(cu, "R"));
    }
}
