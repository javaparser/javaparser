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
        CompilationUnit cu = parse("""
                class Test {
                    public void foo(Object o) {
                        switch (o) {
                            case String s -> System.out.println(s);
                            case null, default -> {}
                        };
                    }
                }\
                """);

        NameExpr name = Navigator.findNameExpression(cu, "s").get();
        assertEquals("java.lang.String", name.resolve().getType().describe());
    }

    @Test
    public void switchPatternWithGuardShouldResolve() {
        CompilationUnit cu = parse("""
                class Test {
                    public void foo(Object o) {
                        switch (o) {
                            case String s when s.length() > 5 -> System.out.println(s);
                            case null, default -> {}
                        };
                    }
                }\
                """);

        cu.findAll(NameExpr.class).stream()
                .filter(nameExpr -> nameExpr.getNameAsString().equals("s"))
                .forEach(nameExpr -> {
                    assertEquals(
                            "java.lang.String", nameExpr.resolve().getType().describe());
                });
    }

    @Test
    public void switchPatternWithNonMatchingNameShouldNotResolve() {
        CompilationUnit cu = parse("""
                class Test {
                    public void foo(Object o) {
                        switch (o) {
                            case String t -> System.out.println(s);
                            case null, default -> {}
                        };
                    }
                }\
                """);

        Executable resolveS = () -> Navigator.findNameExpression(cu, "s").get().resolve();

        assertThrows(UnsolvedSymbolException.class, resolveS);
    }

    @Test
    public void switchPatternInOtherCaseShouldNotResolve() {
        CompilationUnit cu = parse("""
                class Test {
                    public void foo(Object o) {
                        switch (o) {
                            case String t -> {}
                            case Integer i -> System.out.println(t);
                            case null, default -> {}
                        };
                    }
                }\
                """);

        Executable resolveS = () -> Navigator.findNameExpression(cu, "t").get().resolve();

        assertThrows(UnsolvedSymbolException.class, resolveS);
    }

    @Test
    public void nestedSwitchRecordPatternShouldResolve() {
        CompilationUnit cu = parse("""
                class Test {
                    public void foo(Object o) {
                        switch (o) {
                            case Box(InnerBox(Integer i), InnerBox(String s)) -> System.out.println(s);
                            case null, default -> {}
                        };
                    }
                }\
                """);

        NameExpr name = Navigator.findNameExpression(cu, "s").get();
        assertEquals("java.lang.String", name.resolve().getType().describe());
    }

    /**
     * Test that switch expressions used as method arguments can have their type resolved.
     */
    @Test
    public void switchExprAsMethodArgShouldResolveType() {
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        System.out.println(
                            switch ("a") {
                                case "a" -> 3;
                                default -> 0;
                            });
                    }
                }\
                """);

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test that switch expressions returning String can have their type resolved.
     */
    @Test
    public void switchExprReturningStringShouldResolveType() {
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        String result = switch (1) {
                            case 1 -> "one";
                            case 2 -> "two";
                            default -> "other";
                        };
                    }
                }\
                """);

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("java.lang.String", resolvedType.describe());
    }

    /**
     * Test that switch expressions with yield statements can have their type resolved.
     */
    @Test
    public void switchExprWithYieldShouldResolveType() {
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        int result = switch ("x") {
                            case "a" -> 1;
                            default -> {
                                int val = 42;
                                yield val;
                            }
                        };
                    }
                }\
                """);

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test block with multiple yield paths (nested if/else).
     */
    @Test
    public void switchExprWithMultipleYieldPathsShouldResolveType() {
        CompilationUnit cu = parse("""
                class Test {
                    public void test(boolean condition) {
                        int result = switch ("x") {
                            default -> {
                                if (condition) {
                                    yield 1;
                                } else {
                                    yield 2;
                                }
                            }
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        int result = switch ("x") {
                            case "a":
                                yield 1;
                            default:
                                yield 0;
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        int result = switch ("x") {
                            case "a":
                                int val = 42;
                                yield val;
                            default:
                                yield 0;
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        var result = switch (1) {
                            case 1 -> 1;
                            case 2 -> 2L;
                            default -> 0;
                        };
                    }
                }\
                """);

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("long", resolvedType.describe());
    }

    /**
     * Test mixed reference types - String and StringBuilder should LUB to a common supertype.
     */
    @Test
    public void switchExprWithMixedReferenceTypesShouldResolveToLub() {
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        var result = switch (1) {
                            case 1 -> "hello";
                            case 2 -> new StringBuilder();
                            default -> "world";
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        var result = switch (1) {
                            case 1 -> 1;
                            case 2 -> Integer.valueOf(2);
                            default -> 0;
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        int result = switch ("x") {
                            case "error" -> throw new RuntimeException();
                            default -> 42;
                        };
                    }
                }\
                """);

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test switch expression with only default case.
     */
    @Test
    public void switchExprWithDefaultOnlyShouldResolveType() {
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        String result = switch ("x") {
                            default -> "default value";
                        };
                    }
                }\
                """);

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("java.lang.String", resolvedType.describe());
    }

    /**
     * Test nested switch expressions.
     */
    @Test
    public void nestedSwitchExprShouldResolveType() {
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        int result = switch ("outer") {
                            case "outer" -> switch ("inner") {
                                case "inner" -> 1;
                                default -> 2;
                            };
                            default -> 0;
                        };
                    }
                }\
                """);

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test switch expression in cast context.
     */
    @Test
    public void switchExprInCastContextShouldResolveType() {
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        Number result = (Number) switch (1) {
                            case 1 -> 1;
                            default -> 2L;
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test(boolean condition) {
                        int result = condition ? switch (1) {
                            case 1 -> 10;
                            default -> 20;
                        } : 0;
                    }
                }\
                """);

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("int", resolvedType.describe());
    }

    /**
     * Test switch expression as return value.
     */
    @Test
    public void switchExprAsReturnValueShouldResolveType() {
        CompilationUnit cu = parse("""
                class Test {
                    public String test() {
                        return switch (1) {
                            case 1 -> "one";
                            default -> "other";
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        var result = switch (1) {
                            case 1 -> true;
                            case 2 -> Boolean.FALSE;
                            default -> false;
                        };
                    }
                }\
                """);

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("boolean", resolvedType.describe());
    }

    /**
     * Test switch expression where all results are null.
     */
    @Test
    public void switchExprWithAllNullResultsShouldResolveToNullType() {
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        Object result = switch (1) {
                            case 1 -> null;
                            case 2 -> null;
                            default -> null;
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        var result = switch (1) {
                            case 1 -> "hello";
                            case 2 -> null;
                            default -> "world";
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        var result = switch (1) {
                            case 1 -> 42;
                            case 2 -> "hello";
                            default -> 0;
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        int result = switch (1) {
                            case 1 -> throw new IllegalArgumentException();
                            default -> throw new RuntimeException();
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        var result = switch (1) {
                            case 1 -> 1.0f;
                            case 2 -> 2.0;
                            default -> 0;
                        };
                    }
                }\
                """);

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        assertEquals("double", resolvedType.describe());
    }

    /**
     * Test int/float numeric promotion.
     */
    @Test
    public void switchExprWithIntAndFloatShouldResolveToFloat() {
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        var result = switch (1) {
                            case 1 -> 1;
                            case 2 -> 2.0f;
                            default -> 0;
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        int result = switch (1) {
                            case 1:
                            case 2:
                                yield 10;
                            default:
                                yield 0;
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        int result = switch (1) {
                            case 1:
                                yield 10;
                            default:
                                throw new IllegalArgumentException();
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        String result = switch (1) {
                            case 1:
                            case 2:
                            case 3:
                                yield "low";
                            case 4:
                            case 5:
                                yield "high";
                            default:
                                yield "other";
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        String result = switch (1) {
                            case 1:
                                yield "one";
                            case 2:
                                yield "two";
                            default:
                                throw new IllegalArgumentException("unexpected");
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        int result = switch (1) {
                            case 1:
                            case 2:
                                yield 10;
                            case 3:
                                throw new RuntimeException();
                            default:
                                yield 0;
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        int result = switch (1) {
                            case 1 -> {
                                throw new IllegalArgumentException();
                            }
                            default -> 0;
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        int result = switch (1) {
                            case 1 -> {
                                String inner = switch ("x") {
                                    case "a" -> {
                                        yield "inner result";
                                    }
                                    default -> "default";
                                };
                                yield 42;
                            }
                            default -> 0;
                        };
                    }
                }\
                """);

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
        CompilationUnit cu = parse("""
                class Test {
                    public void test() {
                        int result = switch (1) {
                            case 1:
                                String inner = switch ("x") {
                                    case "a":
                                        yield "inner result";
                                    default:
                                        yield "default";
                                };
                                yield 42;
                            default:
                                yield 0;
                        };
                    }
                }\
                """);

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();
        ResolvedType resolvedType = switchExpr.calculateResolvedType();
        // The outer switch should resolve to int (from yield 42), not String (from inner yield)
        assertEquals("int", resolvedType.describe());
    }
}
