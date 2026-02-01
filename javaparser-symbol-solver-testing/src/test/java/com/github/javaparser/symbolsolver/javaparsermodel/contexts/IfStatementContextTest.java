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

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.TypePatternExpr;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.List;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class IfStatementContextTest {

    private final TypeSolver typeSolver = new ReflectionTypeSolver();
    private JavaParser javaParser;

    @BeforeEach
    void beforeEach() {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        javaParser = new JavaParser();
    }

    @Test
    void testInstanceOfWithoutPattern() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    if (o instanceof String) {\n"
                + "        thenCall();\n"
                + "    } else {\n"
                + "        elseCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        IfStmt ifStmt = Navigator.demandNodeOfGivenClass(cu, IfStmt.class);
        IfStatementContext ifContext = new IfStatementContext(ifStmt, typeSolver);

        List<TypePatternExpr> typePatternsExposedToThen =
                ifContext.typePatternExprsExposedToChild(ifStmt.getThenStmt());
        List<TypePatternExpr> typePatternsExposedToElse =
                ifContext.typePatternExprsExposedToChild(ifStmt.getElseStmt().get());
        List<TypePatternExpr> introducedTypePatterns = ifContext.getIntroducedTypePatterns();

        assertEquals(0, typePatternsExposedToThen.size());
        assertEquals(0, typePatternsExposedToElse.size());
        assertEquals(0, introducedTypePatterns.size());
    }

    @Test
    void testInstanceOfWithTypePatternVariableIntroducedToThen() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    if (o instanceof Foo f) {\n"
                + "        thenCall();\n"
                + "    } else {\n"
                + "        elseCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        IfStmt ifStmt = Navigator.demandNodeOfGivenClass(cu, IfStmt.class);
        IfStatementContext ifContext = new IfStatementContext(ifStmt, typeSolver);

        List<TypePatternExpr> typePatternsExposedToThen =
                ifContext.typePatternExprsExposedToChild(ifStmt.getThenStmt());
        List<TypePatternExpr> typePatternsExposedToElse =
                ifContext.typePatternExprsExposedToChild(ifStmt.getElseStmt().get());
        List<TypePatternExpr> introducedTypePatterns = ifContext.getIntroducedTypePatterns();

        assertEquals(1, typePatternsExposedToThen.size());
        TypePatternExpr introducedTypePattern = typePatternsExposedToThen.get(0);
        assertEquals("Foo", introducedTypePattern.getTypeAsString());
        assertEquals("f", introducedTypePattern.getNameAsString());

        assertEquals(0, typePatternsExposedToElse.size());
        assertEquals(0, introducedTypePatterns.size());
    }

    @Test
    void testInstanceOfWithTypePatternVariableIntroducedToElse() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    if (!(o instanceof Foo f)) {\n"
                + "        thenCall();\n"
                + "    } else {\n"
                + "        elseCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        IfStmt ifStmt = Navigator.demandNodeOfGivenClass(cu, IfStmt.class);
        IfStatementContext ifContext = new IfStatementContext(ifStmt, typeSolver);

        List<TypePatternExpr> typePatternsExposedToThen =
                ifContext.typePatternExprsExposedToChild(ifStmt.getThenStmt());
        List<TypePatternExpr> typePatternsExposedToElse =
                ifContext.typePatternExprsExposedToChild(ifStmt.getElseStmt().get());
        List<TypePatternExpr> introducedTypePatterns = ifContext.getIntroducedTypePatterns();

        assertEquals(0, typePatternsExposedToThen.size());

        assertEquals(1, typePatternsExposedToElse.size());
        TypePatternExpr introducedTypePattern = typePatternsExposedToElse.get(0);
        assertEquals("Foo", introducedTypePattern.getTypeAsString());
        assertEquals("f", introducedTypePattern.getNameAsString());

        assertEquals(0, introducedTypePatterns.size());
    }

    @Test
    void testInstanceOfWithTypePatternVariableIntroducedByIf() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    if (!(o instanceof Foo f)) {\n"
                + "        return;\n"
                + "    } else {\n"
                + "        elseCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        IfStmt ifStmt = Navigator.demandNodeOfGivenClass(cu, IfStmt.class);
        IfStatementContext ifContext = new IfStatementContext(ifStmt, typeSolver);

        List<TypePatternExpr> typePatternsExposedToThen =
                ifContext.typePatternExprsExposedToChild(ifStmt.getThenStmt());
        List<TypePatternExpr> typePatternsExposedToElse =
                ifContext.typePatternExprsExposedToChild(ifStmt.getElseStmt().get());
        List<TypePatternExpr> introducedTypePatterns = ifContext.getIntroducedTypePatterns();

        assertEquals(0, typePatternsExposedToThen.size());

        assertEquals(1, typePatternsExposedToElse.size());
        TypePatternExpr typePatternIntroducedToElse = typePatternsExposedToElse.get(0);
        assertEquals("Foo", typePatternIntroducedToElse.getTypeAsString());
        assertEquals("f", typePatternIntroducedToElse.getNameAsString());

        assertEquals(1, introducedTypePatterns.size());
        TypePatternExpr introducedTypePattern = typePatternsExposedToElse.get(0);
        assertEquals("Foo", introducedTypePattern.getTypeAsString());
        assertEquals("f", introducedTypePattern.getNameAsString());
    }

    @Test
    void testInstanceOfWithRecordPatternVariablesIntroducedToThen() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    if (o instanceof Foo (Bar b, Baz (Qux q))) {\n"
                + "        thenCall();\n"
                + "    } else {\n"
                + "        elseCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        IfStmt ifStmt = Navigator.demandNodeOfGivenClass(cu, IfStmt.class);
        IfStatementContext ifContext = new IfStatementContext(ifStmt, typeSolver);

        List<TypePatternExpr> typePatternsExposedToThen =
                ifContext.typePatternExprsExposedToChild(ifStmt.getThenStmt());
        List<TypePatternExpr> typePatternsExposedToElse =
                ifContext.typePatternExprsExposedToChild(ifStmt.getElseStmt().get());
        List<TypePatternExpr> introducedTypePatterns = ifContext.getIntroducedTypePatterns();

        assertEquals(2, typePatternsExposedToThen.size());
        TypePatternExpr barTypePattern = typePatternsExposedToThen.get(0);
        assertEquals("Bar", barTypePattern.getTypeAsString());
        assertEquals("b", barTypePattern.getNameAsString());
        TypePatternExpr quxTypePattern = typePatternsExposedToThen.get(1);
        assertEquals("Qux", quxTypePattern.getTypeAsString());
        assertEquals("q", quxTypePattern.getNameAsString());

        assertEquals(0, typePatternsExposedToElse.size());
        assertEquals(0, introducedTypePatterns.size());
    }

    @Test
    void testInstanceOfWithUnnamedTypePatternVariableIntroducedToThen() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    if (o instanceof Foo _) {\n"
                + "        thenCall();\n"
                + "    } else {\n"
                + "        elseCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        IfStmt ifStmt = Navigator.demandNodeOfGivenClass(cu, IfStmt.class);
        IfStatementContext ifContext = new IfStatementContext(ifStmt, typeSolver);

        List<TypePatternExpr> typePatternsExposedToThen =
                ifContext.typePatternExprsExposedToChild(ifStmt.getThenStmt());
        List<TypePatternExpr> typePatternsExposedToElse =
                ifContext.typePatternExprsExposedToChild(ifStmt.getElseStmt().get());
        List<TypePatternExpr> introducedTypePatterns = ifContext.getIntroducedTypePatterns();

        assertEquals(0, typePatternsExposedToThen.size());
        assertEquals(0, typePatternsExposedToElse.size());
        assertEquals(0, introducedTypePatterns.size());
    }

    @Test
    void testInstanceOfWithMatchAllPatternVariableIntroducedToThen() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    if (o instanceof Foo(_)) {\n"
                + "        thenCall();\n"
                + "    } else {\n"
                + "        elseCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        IfStmt ifStmt = Navigator.demandNodeOfGivenClass(cu, IfStmt.class);
        IfStatementContext ifContext = new IfStatementContext(ifStmt, typeSolver);

        List<TypePatternExpr> typePatternsExposedToThen =
                ifContext.typePatternExprsExposedToChild(ifStmt.getThenStmt());
        List<TypePatternExpr> typePatternsExposedToElse =
                ifContext.typePatternExprsExposedToChild(ifStmt.getElseStmt().get());
        List<TypePatternExpr> introducedTypePatterns = ifContext.getIntroducedTypePatterns();

        assertEquals(0, typePatternsExposedToThen.size());
        assertEquals(0, typePatternsExposedToElse.size());
        assertEquals(0, introducedTypePatterns.size());
    }

    @Test
    void testInstanceOfWithNestedUnnamedTypePatternVariableIntroducedToThen() {
        CompilationUnit cu = parse("class Foo {\n" + "  public void foo(Object o) {\n"
                + "    if (o instanceof Foo(Bar _, Baz(Qux q, _))) {\n"
                + "        thenCall();\n"
                + "    } else {\n"
                + "        elseCall();\n"
                + "    }\n"
                + "  }\n"
                + "}");

        IfStmt ifStmt = Navigator.demandNodeOfGivenClass(cu, IfStmt.class);
        IfStatementContext ifContext = new IfStatementContext(ifStmt, typeSolver);

        List<TypePatternExpr> typePatternsExposedToThen =
                ifContext.typePatternExprsExposedToChild(ifStmt.getThenStmt());
        List<TypePatternExpr> typePatternsExposedToElse =
                ifContext.typePatternExprsExposedToChild(ifStmt.getElseStmt().get());
        List<TypePatternExpr> introducedTypePatterns = ifContext.getIntroducedTypePatterns();

        assertEquals(1, typePatternsExposedToThen.size());
        TypePatternExpr barTypePattern = typePatternsExposedToThen.get(0);
        assertEquals("Qux", barTypePattern.getTypeAsString());
        assertEquals("q", barTypePattern.getNameAsString());
        assertEquals(0, typePatternsExposedToElse.size());
        assertEquals(0, introducedTypePatterns.size());
    }

    private CompilationUnit parse(String sourceCode) {
        return javaParser.parse(sourceCode).getResult().orElseThrow(AssertionError::new);
    }
}
