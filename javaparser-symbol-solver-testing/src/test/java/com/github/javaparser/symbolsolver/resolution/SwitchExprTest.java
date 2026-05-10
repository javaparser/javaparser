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

package com.github.javaparser.symbolsolver.resolution;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.SwitchExpr;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;

public class SwitchExprTest {
    private CompilationUnit parse(String code) {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        parserConfiguration.setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
        return new JavaParser(parserConfiguration).parse(code).getResult().get();
    }

    @Test
    public void switchPatternShouldResolve() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case String s -> System.out.println(s);\n"
                + "            case null, default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        NameExpr name = Navigator.findNameExpression(cu, "s").get();
        assertEquals("java.lang.String", name.resolve().getType().describe());
    }

    @Test
    public void switchPatternWithGuardShouldResolve() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case String s when s.length() > 5 -> System.out.println(s);\n"
                + "            case null, default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        cu.findAll(NameExpr.class).stream()
                .filter(nameExpr -> nameExpr.getNameAsString().equals("s"))
                .forEach(nameExpr -> {
                    assertEquals(
                            "java.lang.String", nameExpr.resolve().getType().describe());
                });
    }

    @Test
    public void switchPatternWithNonMatchingNameShouldNotResolve() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case String t -> System.out.println(s);\n"
                + "            case null, default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        Executable resolveS = () -> Navigator.findNameExpression(cu, "s").get().resolve();

        assertThrows(UnsolvedSymbolException.class, resolveS);
    }

    @Test
    public void switchPatternInOtherCaseShouldNotResolve() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case String t -> {}\n"
                + "            case Integer i -> System.out.println(t);\n"
                + "            case null, default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        Executable resolveS = () -> Navigator.findNameExpression(cu, "t").get().resolve();

        assertThrows(UnsolvedSymbolException.class, resolveS);
    }

    @Test
    public void nestedSwitchRecordPatternShouldResolve() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case Box(InnerBox(Integer i), InnerBox(String s)) -> System.out.println(s);\n"
                + "            case null, default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        NameExpr name = Navigator.findNameExpression(cu, "s").get();
        assertEquals("java.lang.String", name.resolve().getType().describe());
    }

    /**
     * Test that switch expressions used as method arguments can have their type resolved.
     */
    @Test
    public void switchExprAsMethodArgShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        System.out.println(\n"
                + "            switch (\"a\") {\n"
                + "                case \"a\" -> 3;\n"
                + "                default -> 0;\n"
                + "            });\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test that switch expressions returning String can have their type resolved.
     */
    @Test
    public void switchExprReturningStringShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        String result = switch (1) {\n"
                + "            case 1 -> \"one\";\n"
                + "            case 2 -> \"two\";\n"
                + "            default -> \"other\";\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("java.lang.String", resolvedType.describe());
    }

    /**
     * Test that switch expressions with yield statements can have their type resolved.
     */
    @Test
    public void switchExprWithYieldShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        int result = switch (\"x\") {\n"
                + "            case \"a\" -> 1;\n"
                + "            default -> {\n"
                + "                int val = 42;\n"
                + "                yield val;\n"
                + "            }\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test block with multiple yield paths (nested if/else).
     */
    @Test
    public void switchExprWithMultipleYieldPathsShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test(boolean condition) {\n"
                + "        int result = switch (\"x\") {\n"
                + "            default -> {\n"
                + "                if (condition) {\n"
                + "                    yield 1;\n"
                + "                } else {\n"
                + "                    yield 2;\n"
                + "                }\n"
                + "            }\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test colon-style switch expression (STATEMENT_GROUP) with yield.
     * JLS 15.28.1 - "case L:" style requires yield statement.
     */
    @Test
    public void switchExprWithColonStyleShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        int result = switch (\"x\") {\n"
                + "            case \"a\":\n"
                + "                yield 1;\n"
                + "            default:\n"
                + "                yield 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test colon-style switch expression with multiple statements before yield.
     * This tests that we correctly find the yield even when it's not the first statement.
     */
    @Test
    public void switchExprWithColonStyleAndMultipleStatementsShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        int result = switch (\"x\") {\n"
                + "            case \"a\":\n"
                + "                int val = 42;\n"
                + "                yield val;\n"
                + "            default:\n"
                + "                yield 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test mixed primitive types - int and long should LUB to long.
     * JLS 15.28.2 - numeric promotion rules apply.
     */
    @Test
    public void switchExprWithMixedPrimitiveTypesShouldResolveToLub() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        var result = switch (1) {\n"
                + "            case 1 -> 1;\n"
                + "            case 2 -> 2L;\n"
                + "            default -> 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("long", resolvedType.describe());
    }

    /**
     * Test mixed reference types - String and StringBuilder should LUB to a common supertype.
     */
    @Test
    public void switchExprWithMixedReferenceTypesShouldResolveToLub() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        var result = switch (1) {\n"
                + "            case 1 -> \"hello\";\n"
                + "            case 2 -> new StringBuilder();\n"
                + "            default -> \"world\";\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        // String and StringBuilder both implement CharSequence and Serializable
        // LUB should be one of their common supertypes
        assertEquals("java.io.Serializable", resolvedType.describe());
    }

    /**
     * Test mixed boxed and unboxed types - int and Integer.
     */
    @Test
    public void switchExprWithBoxedAndUnboxedTypesShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        var result = switch (1) {\n"
                + "            case 1 -> 1;\n"
                + "            case 2 -> Integer.valueOf(2);\n"
                + "            default -> 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        String type = resolvedType.describe();
        assertTrue(type.equals("int"), "Expected int: " + type);
    }

    /**
     * Test switch expression with throw in a case (THROWS_STATEMENT).
     * The throw case doesn't contribute to the type.
     */
    @Test
    public void switchExprWithThrowCaseShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n" + "    public void test() {\n"
                + "        int result = switch (\"x\") {\n"
                + "            case \"error\" -> throw new RuntimeException();\n"
                + "            default -> 42;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test switch expression with only default case.
     */
    @Test
    public void switchExprWithDefaultOnlyShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n" + "    public void test() {\n"
                + "        String result = switch (\"x\") {\n"
                + "            default -> \"default value\";\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("java.lang.String", resolvedType.describe());
    }

    /**
     * Test nested switch expressions.
     */
    @Test
    public void nestedSwitchExprShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n" + "    public void test() {\n"
                + "        int result = switch (\"outer\") {\n"
                + "            case \"outer\" -> switch (\"inner\") {\n"
                + "                case \"inner\" -> 1;\n"
                + "                default -> 2;\n"
                + "            };\n"
                + "            default -> 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test switch expression in cast context.
     */
    @Test
    public void switchExprInCastContextShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n" + "    public void test() {\n"
                + "        Number result = (Number) switch (1) {\n"
                + "            case 1 -> 1;\n"
                + "            default -> 2L;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        // As a standalone expression, the type is determined by LUB of int and long
        assertEquals("long", resolvedType.describe());
    }

    /**
     * Test switch expression in ternary conditional.
     */
    @Test
    public void switchExprInTernaryContextShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n" + "    public void test(boolean condition) {\n"
                + "        int result = condition ? switch (1) {\n"
                + "            case 1 -> 10;\n"
                + "            default -> 20;\n"
                + "        } : 0;\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test switch expression as return value.
     */
    @Test
    public void switchExprAsReturnValueShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public String test() {\n"
                + "        return switch (1) {\n"
                + "            case 1 -> \"one\";\n"
                + "            default -> \"other\";\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("java.lang.String", resolvedType.describe());
    }

    /**
     * Test mixed boolean and Boolean types.
     * JLS 15.28.2 - If each result is boolean or Boolean, unbox to boolean.
     */
    @Test
    public void switchExprWithMixedBooleanTypesShouldResolveToBoolean() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        var result = switch (1) {\n"
                + "            case 1 -> true;\n"
                + "            case 2 -> Boolean.FALSE;\n"
                + "            default -> false;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("boolean", resolvedType.describe());
    }

    /**
     * Test switch expression where all results are null.
     */
    @Test
    public void switchExprWithAllNullResultsShouldResolveToNullType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        Object result = switch (1) {\n"
                + "            case 1 -> null;\n"
                + "            case 2 -> null;\n"
                + "            default -> null;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("null", resolvedType.describe());
    }

    /**
     * Test null mixed with reference type.
     * LUB of String and null should be String.
     */
    @Test
    public void switchExprWithNullAndReferenceTypeShouldResolveToReferenceType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        var result = switch (1) {\n"
                + "            case 1 -> \"hello\";\n"
                + "            case 2 -> null;\n"
                + "            default -> \"world\";\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("java.lang.String", resolvedType.describe());
    }

    /**
     * Test JLS rule 4: primitive boxed before LUB with incompatible reference type.
     * int should be boxed to Integer, then LUB with String computed.
     */
    @Test
    public void switchExprWithPrimitiveAndReferenceTypeShouldBoxThenLub() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        var result = switch (1) {\n"
                + "            case 1 -> 42;\n"
                + "            case 2 -> \"hello\";\n"
                + "            default -> 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        // LUB of Integer and String is Serializable (both implement it)
        assertEquals("java.io.Serializable", resolvedType.describe());
    }

    /**
     * Test switch expression where all cases throw.
     * Since all branches throw, there are no result expressions to determine the type from.
     * This is not valid Java code - the validator should catch it.
     */
    @Test
    public void switchExprWithAllThrowsShouldBeInvalid() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        int result = switch (1) {\n"
                + "            case 1 -> throw new IllegalArgumentException();\n"
                + "            default -> throw new RuntimeException();\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        // When all cases throw, there are no result expressions to infer the type from.
        // This should be caught earlier by the validator, but here we check that type resolution fails.
        assertThrows(IllegalStateException.class, switchExpr::calculateResolvedType);
    }

    /**
     * Test float/double numeric promotion.
     * JLS 15.28.2 - numeric promotion with float and double.
     */
    @Test
    public void switchExprWithFloatAndDoubleShouldResolveToDouble() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        var result = switch (1) {\n"
                + "            case 1 -> 1.0f;\n"
                + "            case 2 -> 2.0;\n"
                + "            default -> 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("double", resolvedType.describe());
    }

    /**
     * Test int/float numeric promotion.
     */
    @Test
    public void switchExprWithIntAndFloatShouldResolveToFloat() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        var result = switch (1) {\n"
                + "            case 1 -> 1;\n"
                + "            case 2 -> 2.0f;\n"
                + "            default -> 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("float", resolvedType.describe());
    }

    /**
     * Test colon-style switch expression with fall-through cases.
     * The first case falls through to the second case which has the yield.
     */
    @Test
    public void switchExprWithColonStyleFallThroughShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        int result = switch (1) {\n"
                + "            case 1:\n"
                + "            case 2:\n"
                + "                yield 10;\n"
                + "            default:\n"
                + "                yield 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test colon-style switch expression where a case throws instead of yielding.
     * The throw case doesn't contribute to the type, similar to arrow-style throws.
     */
    @Test
    public void switchExprWithColonStyleThrowShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        int result = switch (1) {\n"
                + "            case 1:\n"
                + "                yield 10;\n"
                + "            default:\n"
                + "                throw new IllegalArgumentException();\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test colon-style switch expression with multiple fall-through cases.
     * Cases 1, 2, and 3 all fall through to case 3's yield.
     */
    @Test
    public void switchExprWithColonStyleMultipleFallThroughShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        String result = switch (1) {\n"
                + "            case 1:\n"
                + "            case 2:\n"
                + "            case 3:\n"
                + "                yield \"low\";\n"
                + "            case 4:\n"
                + "            case 5:\n"
                + "                yield \"high\";\n"
                + "            default:\n"
                + "                yield \"other\";\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("java.lang.String", resolvedType.describe());
    }

    /**
     * Test colon-style switch expression where default throws.
     * Only the regular cases contribute to the type.
     */
    @Test
    public void switchExprWithColonStyleDefaultThrowsShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        String result = switch (1) {\n"
                + "            case 1:\n"
                + "                yield \"one\";\n"
                + "            case 2:\n"
                + "                yield \"two\";\n"
                + "            default:\n"
                + "                throw new IllegalArgumentException(\"unexpected\");\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("java.lang.String", resolvedType.describe());
    }

    /**
     * Test colon-style switch expression with mixed fall-through and throw.
     * Case 1 falls through to case 2 which yields, case 3 throws.
     */
    @Test
    public void switchExprWithColonStyleMixedFallThroughAndThrowShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        int result = switch (1) {\n"
                + "            case 1:\n"
                + "            case 2:\n"
                + "                yield 10;\n"
                + "            case 3:\n"
                + "                throw new RuntimeException();\n"
                + "            default:\n"
                + "                yield 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test arrow-style switch expression where a block throws instead of yielding.
     * The throwing block doesn't contribute to the type.
     */
    @Test
    public void switchExprWithBlockThrowShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        int result = switch (1) {\n"
                + "            case 1 -> {\n"
                + "                throw new IllegalArgumentException();\n"
                + "            }\n"
                + "            default -> 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test nested switch expressions in blocks.
     * The outer switch should find its own yield, not the inner switch's yield.
     */
    @Test
    public void switchExprWithNestedSwitchInBlockShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        int result = switch (1) {\n"
                + "            case 1 -> {\n"
                + "                String inner = switch (\"x\") {\n"
                + "                    case \"a\" -> {\n"
                + "                        yield \"inner result\";\n"
                + "                    }\n"
                + "                    default -> \"default\";\n"
                + "                };\n"
                + "                yield 42;\n"
                + "            }\n"
                + "            default -> 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        // The outer switch should resolve to int (from yield 42), not String (from inner yield)
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test nested switch expressions in colon-style (STATEMENT_GROUP).
     * The outer switch should find its own yield, not the inner switch's yield.
     */
    @Test
    public void switchExprWithNestedSwitchInStatementGroupShouldResolveType() {
        CompilationUnit cu = parse("class Test {\n"
                + "    public void test() {\n"
                + "        int result = switch (1) {\n"
                + "            case 1:\n"
                + "                String inner = switch (\"x\") {\n"
                + "                    case \"a\":\n"
                + "                        yield \"inner result\";\n"
                + "                    default:\n"
                + "                        yield \"default\";\n"
                + "                };\n"
                + "                yield 42;\n"
                + "            default:\n"
                + "                yield 0;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        // The outer switch should resolve to int (from yield 42), not String (from inner yield)
        assertEquals("int", resolvedType.describe());
    }
}
