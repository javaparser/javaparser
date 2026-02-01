/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2025 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.TypePatternExpr;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.List;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class SwitchStatementContextTest {

    private final TypeSolver typeSolver = new ReflectionTypeSolver();
    private JavaParser javaParser;

    @BeforeEach
    void beforeEach() {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        javaParser = new JavaParser();
    }

    @Test
    void testSwitchWithoutPattern() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    switch (o) {\n"
                + "        case 12 -> someCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        SwitchEntry switchEntry = Navigator.demandNodeOfGivenClass(cu, SwitchEntry.class);
        SwitchEntryContext entryContext = new SwitchEntryContext(switchEntry, typeSolver);

        List<TypePatternExpr> typePatternsExposedToBody =
                entryContext.typePatternExprsExposedToChild(switchEntry.getStatement(0));

        assertEquals(0, typePatternsExposedToBody.size());
    }

    @Test
    void testSwitchWithTypePattern() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    switch (o) {\n"
                + "        case Foo f -> someCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        SwitchEntry switchEntry = Navigator.demandNodeOfGivenClass(cu, SwitchEntry.class);
        SwitchEntryContext entryContext = new SwitchEntryContext(switchEntry, typeSolver);

        List<TypePatternExpr> typePatternsExposedToBody =
                entryContext.typePatternExprsExposedToChild(switchEntry.getStatement(0));

        assertEquals(1, typePatternsExposedToBody.size());
        TypePatternExpr exposedPattern = typePatternsExposedToBody.get(0);
        assertEquals("Foo", exposedPattern.getTypeAsString());
        assertEquals("f", exposedPattern.getNameAsString());
    }

    @Test
    void testSwitchWithUnnamedTypePattern() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    switch (o) {\n"
                + "        case Foo _ -> someCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        SwitchEntry switchEntry = Navigator.demandNodeOfGivenClass(cu, SwitchEntry.class);
        SwitchEntryContext entryContext = new SwitchEntryContext(switchEntry, typeSolver);

        List<TypePatternExpr> typePatternsExposedToBody =
                entryContext.typePatternExprsExposedToChild(switchEntry.getStatement(0));

        assertEquals(0, typePatternsExposedToBody.size());
    }

    @Test
    void testSwitchWithRecordPattern() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    switch (o) {\n"
                + "        case Foo(Bar b, Qux(Quux q)) -> someCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        SwitchEntry switchEntry = Navigator.demandNodeOfGivenClass(cu, SwitchEntry.class);
        SwitchEntryContext entryContext = new SwitchEntryContext(switchEntry, typeSolver);

        List<TypePatternExpr> typePatternsExposedToBody =
                entryContext.typePatternExprsExposedToChild(switchEntry.getStatement(0));

        assertEquals(2, typePatternsExposedToBody.size());
        TypePatternExpr exposedPattern = typePatternsExposedToBody.get(0);
        assertEquals("Bar", exposedPattern.getTypeAsString());
        assertEquals("b", exposedPattern.getNameAsString());
        TypePatternExpr secondExposedPattern = typePatternsExposedToBody.get(1);
        assertEquals("Quux", secondExposedPattern.getTypeAsString());
        assertEquals("q", secondExposedPattern.getNameAsString());
    }

    @Test
    void testSwitchWithMatchAllPattern() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    switch (o) {\n"
                + "        case Foo(Bar b, Qux(Quux _)) -> someCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        SwitchEntry switchEntry = Navigator.demandNodeOfGivenClass(cu, SwitchEntry.class);
        SwitchEntryContext entryContext = new SwitchEntryContext(switchEntry, typeSolver);

        List<TypePatternExpr> typePatternsExposedToBody =
                entryContext.typePatternExprsExposedToChild(switchEntry.getStatement(0));

        assertEquals(1, typePatternsExposedToBody.size());
        TypePatternExpr exposedPattern = typePatternsExposedToBody.get(0);
        assertEquals("Bar", exposedPattern.getTypeAsString());
        assertEquals("b", exposedPattern.getNameAsString());
    }

    private CompilationUnit parse(String sourceCode) {
        return javaParser.parse(sourceCode).getResult().orElseThrow(AssertionError::new);
    }
}
