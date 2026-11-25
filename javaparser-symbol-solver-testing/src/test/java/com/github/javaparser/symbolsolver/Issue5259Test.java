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
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Issue #5259: the types of the {@code permits} clause (JLS 8.1.6, JLS 9.1.4) must not be resolved against the
 * member types of the sealed declaration, whose scope is the body of the declaration (JLS 6.3): they are resolved
 * from the enclosing scope. The expected types are the ones reported by javac 17 for the same sources.
 */
class Issue5259Test {

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

    /** The types of the permits clause of the declaration, resolved one by one. */
    private static List<String> permittedTypes(CompilationUnit cu, String simpleName) {
        return cu
                .findFirst(ClassOrInterfaceDeclaration.class, c -> c.getNameAsString()
                        .equals(simpleName))
                .get()
                .getPermittedTypes()
                .stream()
                .map(type -> type.resolve().describe())
                .collect(Collectors.toList());
    }

    @Test
    void permitsTheTopLevelTypeRatherThanTheMemberTypeWithTheSameName() {
        CompilationUnit cu = parse("final class A implements S {}\n"
                + "sealed interface S permits A { interface A {} }\n"
                + "final class B extends Q {}\n"
                + "sealed class Q permits B { static class B {} }");

        assertEquals(Arrays.asList("A"), permittedTypes(cu, "S"));
        assertEquals(Arrays.asList("B"), permittedTypes(cu, "Q"));
    }

    @Test
    void typesDeclaredInTheEnclosingTypeAreStillPermitted() {
        CompilationUnit cu = parse("class Outer { sealed interface S permits A {} final class A implements S {} }");

        assertEquals(Arrays.asList("Outer.A"), permittedTypes(cu, "S"));
    }

    @Test
    void memberTypesQualifiedByTheSealedTypeAreStillPermitted() {
        CompilationUnit cu = parse("sealed interface S permits S.A { final class A implements S {} }");

        assertEquals(Arrays.asList("S.A"), permittedTypes(cu, "S"));
    }
}
