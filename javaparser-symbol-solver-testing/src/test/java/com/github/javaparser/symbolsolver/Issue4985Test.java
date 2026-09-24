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
import static org.junit.jupiter.api.Assertions.assertThrows;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.io.IOException;
import java.nio.file.Path;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * An ancestor that cannot be resolved only hides its own members: the rest of the hierarchy stays usable, however
 * deep the unresolvable ancestor lies. Here {@code Millisecond extends RegularTimePeriod}, which implements an
 * interface that the type solver cannot find.
 */
public class Issue4985Test extends AbstractSymbolResolutionTest {

    private Path issueResourcesPath;
    private CombinedTypeSolver typeSolver;
    private JavaParser parser;

    @BeforeEach
    void setUp() {
        issueResourcesPath = adaptPath("src/test/resources/issue4985");
        typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JavaParserTypeSolver(issueResourcesPath));
        parser = new JavaParser(new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver)));
    }

    @Test
    void aMethodDeclaredInTheSubclassIsSolved() throws IOException {
        assertEquals("org.jfree.data.time.Millisecond.getMillisecond()", solveCall("getMillisecond"));
    }

    @Test
    void aMethodInheritedFromTheClassWithTheUnresolvableAncestorIsSolved() throws IOException {
        assertEquals("org.jfree.data.time.RegularTimePeriod.getEnd()", solveCall("getEnd"));
    }

    @Test
    void aMethodInheritedFromObjectIsSolved() throws IOException {
        assertEquals("java.lang.Object.hashCode()", solveCall("hashCode"));
    }

    @Test
    void theSubclassIsAssignableToTheClassWithTheUnresolvableAncestor() throws IOException {
        assertEquals(
                "org.jfree.data.time.MillisecondUser.acceptPeriod(org.jfree.data.time.RegularTimePeriod)",
                solveCall("acceptPeriod"));
    }

    @Test
    void anAssignabilityThatTheResolvableAncestorsCannotProveStillReportsTheUnresolvableAncestor() throws IOException {
        MethodCallExpr call = findCall("acceptString");

        UnsolvedSymbolException e = assertThrows(UnsolvedSymbolException.class, call::resolve);
        assertEquals("MonthConstants", e.getName());
    }

    @Test
    void theFieldsOfTheClassWithTheUnresolvableAncestorAreVisibleToInheritors() {
        ResolvedReferenceTypeDeclaration regularTimePeriod =
                typeSolver.solveType("org.jfree.data.time.RegularTimePeriod");

        List<String> fieldNames = new ReferenceTypeImpl(regularTimePeriod)
                .getAllFieldsVisibleToInheritors().stream()
                        .map(ResolvedFieldDeclaration::getName)
                        .collect(Collectors.toList());

        assertEquals(Collections.singletonList("pegged"), fieldNames);
    }

    @Test
    void aMemberOfTheUnresolvableAncestorStaysUnsolved() throws IOException {
        FieldAccessExpr january =
                parse("MillisecondUser").findFirst(FieldAccessExpr.class).get();

        assertThrows(UnsolvedSymbolException.class, january::resolve);
    }

    private String solveCall(String methodName) throws IOException {
        return findCall(methodName).resolve().getQualifiedSignature();
    }

    private MethodCallExpr findCall(String methodName) throws IOException {
        return parse("MillisecondUser")
                .findFirst(MethodCallExpr.class, call -> call.getNameAsString().equals(methodName))
                .get();
    }

    private CompilationUnit parse(String className) throws IOException {
        return parser.parse(issueResourcesPath.resolve("org/jfree/data/time/" + className + ".java"))
                .getResult()
                .get();
    }
}
