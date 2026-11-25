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
import com.github.javaparser.ast.body.TypeDeclaration;
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
 * Issue #5268: a comment inside the qualified name of a supertype is not part of the name, since comments are
 * discarded before the tokens are given to the syntactic grammar (JLS 3.2, JLS 3.5). The expected types are the ones
 * reported by javac 17 for the same sources.
 */
class Issue5268Test {

    private JavaParser javaParser;

    @BeforeEach
    void setup() {
        JavaParserFacade.clearInstances();
        ParserConfiguration configuration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17)
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        javaParser = new JavaParser(configuration);
    }

    private List<String> ancestors(String code) {
        return javaParser
                .parse(code)
                .getResult()
                .get()
                .findFirst(TypeDeclaration.class)
                .get()
                .resolve()
                .getAncestors()
                .stream()
                .map(ResolvedReferenceType::describe)
                .collect(Collectors.toList());
    }

    @Test
    void commentInTheQualifiedNameOfAnImplementedInterfaceOfAClass() {
        assertEquals(
                Arrays.asList("java.lang.Object", "java.util.RandomAccess"),
                ancestors("class C implements java /* c */ .util.RandomAccess {}"));
    }

    @Test
    void endOfLineCommentInTheQualifiedNameOfAnImplementedInterfaceOfAClass() {
        assertEquals(
                Arrays.asList("java.lang.Object", "java.util.RandomAccess"),
                ancestors("class C implements java.util // c\n .RandomAccess {}"));
    }

    @Test
    void commentInTheQualifiedNameOfTheSuperclass() {
        assertEquals(
                Arrays.asList("java.util.ArrayList<java.lang.String>"),
                ancestors("class C extends java /* c */ .util.ArrayList<String> {}"));
    }

    @Test
    void commentInTheQualifiedNameOfAnImplementedInterfaceOfAnEnum() {
        assertEquals(
                Arrays.asList("java.lang.Enum<C>", "java.util.RandomAccess"),
                ancestors("enum C implements java /* c */ .util.RandomAccess {}"));
    }

    /** The ancestors of a record include java.lang.Record, which the reflection type solver finds from Java 14. */
    @Test
    @EnabledForJreRange(min = JRE.JAVA_14)
    void commentInTheQualifiedNameOfAnImplementedInterfaceOfARecord() {
        assertEquals(
                Arrays.asList("java.lang.Record", "java.util.RandomAccess"),
                ancestors("record C() implements java /* c */ .util.RandomAccess {}"));
    }

    @Test
    void commentInTheQualifiedNameOfAnExtendedInterfaceOfAnInterface() {
        assertEquals(
                Arrays.asList("java.util.RandomAccess"),
                ancestors("interface C extends java /* c */ .util.RandomAccess {}"));
    }
}
