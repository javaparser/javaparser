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
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Issue #5264: in the extends clause of an interface (JLS 9.1.3), a qualified type name whose first identifier names
 * a type in scope denotes a member of that type, since a type is chosen in preference to a package of the same name
 * (JLS 6.4.2). The expected types are the ones reported by javac 17 for the same sources.
 */
class Issue5264Test {

    private static final String TYPE_NAMED_LIKE_A_PACKAGE = "class java { interface util { interface List {} } }\n"
            + "interface I extends java.util.List {}\n"
            + "class C implements java.util.List {}";

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

    private static ClassOrInterfaceDeclaration declaration(CompilationUnit cu, String simpleName) {
        return cu.findFirst(ClassOrInterfaceDeclaration.class, c -> c.getNameAsString()
                        .equals(simpleName))
                .get();
    }

    /** The nodes declaring the ancestors, empty for the types that are not declared in the source. */
    private static List<Optional<Node>> ancestorNodes(CompilationUnit cu, String simpleName) {
        return declaration(cu, simpleName).resolve().getAncestors().stream()
                .map(ancestor -> ancestor.getTypeDeclaration().get().toAst())
                .collect(Collectors.toList());
    }

    @Test
    void qualifiedNameInTheExtendsClauseOfAnInterfaceDenotesTheTypeInScope() {
        CompilationUnit cu = parse(TYPE_NAMED_LIKE_A_PACKAGE);

        assertEquals(Arrays.asList(Optional.of(declaration(cu, "List"))), ancestorNodes(cu, "I"));
    }

    @Test
    void qualifiedNameInTheImplementsClauseOfAClassStillDenotesTheTypeInScope() {
        CompilationUnit cu = parse(TYPE_NAMED_LIKE_A_PACKAGE);

        assertEquals(Arrays.asList(Optional.empty(), Optional.of(declaration(cu, "List"))), ancestorNodes(cu, "C"));
    }

    @Test
    void fullyQualifiedNameOfALibraryTypeIsStillResolved() {
        CompilationUnit cu = parse("interface I extends java.io.Serializable, java.util.Comparator<String> {}");

        assertEquals(
                Arrays.asList("java.io.Serializable", "java.util.Comparator<java.lang.String>"),
                declaration(cu, "I").resolve().getAncestors().stream()
                        .map(ResolvedReferenceType::describe)
                        .collect(Collectors.toList()));
    }

    @Test
    void qualifiedNameOfAMemberTypeIsStillResolved() {
        CompilationUnit cu = parse("class Outer { interface J {} }\ninterface I extends Outer.J {}");

        assertEquals(Arrays.asList(Optional.of(declaration(cu, "J"))), ancestorNodes(cu, "I"));
    }
}
