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
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Issue #5272: a qualified type name M.X denotes the member type X of M (JLS 6.5.5.2), whatever the kind of the
 * member type M. The expected types are the ones reported by javac 17 for the same sources.
 */
class Issue5272Test {

    private JavaParser javaParser;

    @BeforeEach
    void setup() {
        JavaParserFacade.clearInstances();
        ParserConfiguration configuration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17)
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        javaParser = new JavaParser(configuration);
    }

    /** The type of a field named through M, a member type of Sub inherited by D from Base. */
    private String fieldTypeThroughInheritedMemberType(String memberType) {
        CompilationUnit cu = javaParser
                .parse("class Base { static class Sub { " + memberType + " } }\nclass D extends Base { Sub.M.X f; }")
                .getResult()
                .get();
        return cu.getClassByName("D")
                .get()
                .getFields()
                .get(0)
                .getVariable(0)
                .getType()
                .resolve()
                .describe();
    }

    /** The type named M.X from the declaration of the class O, of which M is a member type. */
    private String typeSolvedFromTheDeclaration(String memberType) {
        CompilationUnit cu =
                javaParser.parse("class O { " + memberType + " }").getResult().get();
        return new JavaParserClassDeclaration(cu.getClassByName("O").get(), new ReflectionTypeSolver())
                .solveType("M.X")
                .getCorrespondingDeclaration()
                .getQualifiedName();
    }

    @Test
    void memberTypeOfAMemberEnum() {
        assertEquals("Base.Sub.M.X", fieldTypeThroughInheritedMemberType("enum M { A; class X {} }"));
        assertEquals("O.M.X", typeSolvedFromTheDeclaration("enum M { A; class X {} }"));
    }

    @Test
    void memberTypeOfAMemberRecord() {
        assertEquals("Base.Sub.M.X", fieldTypeThroughInheritedMemberType("record M() { class X {} }"));
        assertEquals("O.M.X", typeSolvedFromTheDeclaration("record M() { class X {} }"));
    }

    @Test
    void memberTypeOfAMemberAnnotationInterface() {
        assertEquals("Base.Sub.M.X", fieldTypeThroughInheritedMemberType("@interface M { class X {} }"));
        assertEquals("O.M.X", typeSolvedFromTheDeclaration("@interface M { class X {} }"));
    }

    @Test
    void memberTypeOfAMemberClassIsStillResolved() {
        assertEquals("Base.Sub.M.X", fieldTypeThroughInheritedMemberType("static class M { class X {} }"));
        assertEquals("O.M.X", typeSolvedFromTheDeclaration("static class M { class X {} }"));
    }

    @Test
    void memberTypeOfAMemberInterfaceIsStillResolved() {
        assertEquals("Base.Sub.M.X", fieldTypeThroughInheritedMemberType("interface M { class X {} }"));
        assertEquals("O.M.X", typeSolvedFromTheDeclaration("interface M { class X {} }"));
    }
}
