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
 * Issue #5273: a qualified type name M.X denotes the member type X of M (JLS 6.5.5.2), including a member type that M
 * inherits from its superclass or a superinterface (JLS 8.5, JLS 9.5). The expected types are the ones reported by
 * javac 17 for the same sources.
 */
class Issue5273Test {

    private static final String SUPERTYPES = "\nclass Base2 { class X {} }\ninterface I2 { class X {} }";

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
                .parse("class Base { static class Sub { " + memberType + " } }\nclass D extends Base { Sub.M.X f; }"
                        + SUPERTYPES)
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
        CompilationUnit cu = javaParser
                .parse("class O { " + memberType + " }" + SUPERTYPES)
                .getResult()
                .get();
        return new JavaParserClassDeclaration(cu.getClassByName("O").get(), new ReflectionTypeSolver())
                .solveType("M.X")
                .getCorrespondingDeclaration()
                .getQualifiedName();
    }

    @Test
    void memberTypeInheritedByAMemberClass() {
        assertEquals("Base2.X", fieldTypeThroughInheritedMemberType("static class M extends Base2 {}"));
        assertEquals("Base2.X", typeSolvedFromTheDeclaration("static class M extends Base2 {}"));
    }

    @Test
    void memberTypeInheritedByAMemberInterface() {
        assertEquals("I2.X", fieldTypeThroughInheritedMemberType("interface M extends I2 {}"));
        assertEquals("I2.X", typeSolvedFromTheDeclaration("interface M extends I2 {}"));
    }

    @Test
    void memberTypeInheritedByAMemberEnum() {
        assertEquals("I2.X", fieldTypeThroughInheritedMemberType("enum M implements I2 { A }"));
        assertEquals("I2.X", typeSolvedFromTheDeclaration("enum M implements I2 { A }"));
    }

    @Test
    void memberTypeInheritedByAMemberRecord() {
        assertEquals("I2.X", fieldTypeThroughInheritedMemberType("record M() implements I2 {}"));
        assertEquals("I2.X", typeSolvedFromTheDeclaration("record M() implements I2 {}"));
    }
}
