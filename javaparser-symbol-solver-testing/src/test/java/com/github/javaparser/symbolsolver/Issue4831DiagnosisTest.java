/*
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typesolvers.TypeSolverBuilder;
import java.util.HashMap;
import java.util.Map;
import org.junit.jupiter.api.Test;

/**
 * Issue #4831 的分层诊断：每个测试使用独立 AST，不依赖测试执行顺序或其他测试留下的缓存。
 * 失败表示该路径没有得到预期类型；多个层次共用推断代码，不能仅凭一个失败就认定根因。
 * 完整复现的遍历顺序由 Issue4831Test 保留，这里刻意单独查询不同中间结果。
 */
class Issue4831DiagnosisTest extends AbstractSymbolResolutionTest {

    // A 组：先排除 Lambda 和链式调用，只检查普通方法调用中的泛型推断。

    // A1：基础对照。失败时先检查普通 T 的绑定及返回类型替换。
    @Test
    void A1_inferWithoutWildcard() {
        assertCallType(listCode("List<T>", "List<String>"), "first", "java.lang.String");
    }

    // A2：仅增加一层 ? extends T；与 A1 比较通配符匹配路径。
    @Test
    void A2_inferWithExtendsWildcard() {
        assertCallType(listCode("List<? extends T>", "List<String>"), "first", "java.lang.String");
    }

    // A3：嵌套通配符；与 A2 比较递归匹配及内层 T 的绑定。
    @Test
    void A3_inferWithNestedExtendsWildcards() {
        assertCallType(
                listCode("List<? extends List<? extends T>>", "List<List<String>>"),
                "first",
                "java.lang.String");
    }

    // A4：绕过方法调用上下文，直接检查 inferTypes(actual, formal, mappings)。
    @Test
    void A4_testInferTypesDirectly() {
        CompilationUnit cu = parse(listCode("List<? extends T>", "List<String>"));

        MethodDeclaration first = findMethod(cu, "first");
        MethodDeclaration test = findMethod(cu, "test");

        ResolvedMethodDeclaration declaration = first.resolve();

        ResolvedType formalType = declaration.getParam(0).getType();

        ResolvedType actualType = test.resolve().getParam(0).getType();

        Map<ResolvedTypeParameterDeclaration, ResolvedType> mappings = new HashMap<>();

        // source 是实参类型，target 是含 T 的形参类型；此测试只覆盖单层 extends。
        MethodResolutionLogic.inferTypes(actualType, formalType, mappings);

        ResolvedTypeParameterDeclaration typeParameter = declaration.getTypeParameters().get(0);

        ResolvedType inferred = mappings.get(typeParameter);

        assertNotNull(inferred, "No mapping was produced for T");
        assertEquals("java.lang.String", inferred.describe());
    }

    // B 组：只查询 defer 的返回类型，避免 consume 和第二个 Lambda 干扰诊断。


    @Test
    void B0_supplierWithoutWildcardOrLambda() {
        assertCallType(
                monoCode(
                        "Supplier<Mono<T>>",
                        "Supplier<Mono<String>> supplier = null;"
                                + " Mono.defer(supplier);"),
                "defer",
                "Foo.Mono<java.lang.String>");
    }

    // B1：Supplier 由方法参数提供，源码中没有 Lambda，仅检查泛型实参与形参匹配。
    @Test
    void B1_deferWithSupplierVariable() {
        assertCallType(
                monoCode(
                        "Supplier<? extends Mono<? extends T>>",
                        "Supplier<Mono<String>> supplier",
                        "Mono.defer(supplier);"),
                "defer",
                "Foo.Mono<java.lang.String>");
    }

    // B2：不含通配符的 Lambda 对照，检查返回表达式 Mono<String> 的类型推断。
    @Test
    void B2_deferLambdaWithoutWildcards() {
        assertCallType(
                monoCode("Supplier<Mono<T>>", "Mono.defer(() -> (Mono<String>) null);"),
                "defer",
                "Foo.Mono<java.lang.String>");
    }

    // B3：在 B2 上加入嵌套通配符，检查 Lambda 返回值与通配符的组合。
    @Test
    void B3_deferLambdaWithWildcards() {
        assertCallType(
                monoCode(
                        "Supplier<? extends Mono<? extends T>>",
                        "Mono.defer(() -> (Mono<String>) null);"),
                "defer",
                "Foo.Mono<java.lang.String>");
    }

    // B4：显式指定 String，检查显式类型参数能否替换 defer 的方法类型变量。
    @Test
    void B4_deferWithExplicitTypeArgument() {
        assertCallType(
                monoCode(
                        "Supplier<? extends Mono<? extends T>>",
                        "Mono.<String>defer(() -> null);"),
                "defer",
                "Foo.Mono<java.lang.String>");
    }



    @Test
    void B5_supplierWithOuterWildcardOnly() {
        assertCallType(
                monoCode(
                        "Supplier<? extends Mono<T>>",
                        "Supplier<Mono<String>> supplier = null;"
                                + " Mono.defer(supplier);"),
                "defer",
                "Foo.Mono<java.lang.String>");
    }

    @Test
    void B6_supplierWithInnerWildcardOnly() {
        assertCallType(
                monoCode(
                        "Supplier<Mono<? extends T>>",
                        "Supplier<Mono<? extends String>> supplier = null;"
                                + " Mono.defer(supplier);"),
                "defer",
                "Foo.Mono<java.lang.String>");
    }

    // C 组：查询第二个 Lambda 中 NameExpr s 的类型，不主动解析 length()。

    // C1：接收者已知为 Mono<String>，检查 Consumer<? super T> 对 s 的目标类型传递。
    @Test
    void C1_consumerWithConcreteMono() {
        assertLambdaParameterType(
                monoCode(
                        "Supplier<? extends Mono<? extends T>>",
                        "Mono<String> mono = null; mono.consume(s -> s.length());"),
                "java.lang.String");
    }

    // C2：通过显式 defer<String> 得到接收者，检查链式调用是否保留 String。
    @Test
    void C2_consumerAfterExplicitDefer() {
        assertLambdaParameterType(
                monoCode(
                        "Supplier<? extends Mono<? extends T>>",
                        "Mono.<String>defer(() -> null).consume(s -> s.length());"),
                "java.lang.String");
    }

    // C3：自动推断的完整链；若 B3 已失败，应先检查 defer 的返回类型。
    @Test
    void C3_consumerAfterInferredDefer() {
        assertLambdaParameterType(
                monoCode(
                        "Supplier<? extends Mono<? extends T>>",
                        "Mono.defer(() -> (Mono<String>) null).consume(s -> s.length());"),
                "java.lang.String");
    }

    // D 组：用直接 String 调用作对照，再检查完整链上的最终方法解析。

    // D0：不含泛型或 Lambda 的 String.length() 基础对照。
    @Test
    void D0_resolveStringLengthWithoutGenericInference() {
        CompilationUnit cu = parse("class Example { void test(String s) { s.length(); } }");
        assertStringLength(findCall(cu, "length"));
    }

    // D1：完整链的最终检查；失败也可能来自上游，需结合 B3、C3 和 D0 判断。
    @Test
    void D1_resolveStringLengthInFullChain() {
        CompilationUnit cu = parse(monoCode(
                "Supplier<? extends Mono<? extends T>>",
                "Mono.defer(() -> (Mono<String>) null).consume(s -> s.length());"));

        MethodCallExpr length = findCall(cu, "length");

        assertStringLength(length);
    }

    @Test
    void E1_directInferenceWithOuterWildcard() {
        assertDirectSupplierInference(
                "Supplier<? extends Mono<T>>",
                "Supplier<Mono<String>>");
    }

    @Test
    void E2_directInferenceWithInnerWildcard() {
        assertDirectSupplierInference(
                "Supplier<Mono<? extends T>>",
                "Supplier<Mono<? extends String>>");
    }

    private void assertDirectSupplierInference(
            String formal,
            String actual) {

        String code = "import java.util.function.Supplier;\n"
                + "class Example {\n"
                + "    static class Mono<T> {}\n"
                + "    static <T> Mono<T> defer("
                + formal + " supplier) { return null; }\n"
                + "    void test(" + actual + " supplier) {\n"
                + "        defer(supplier);\n"
                + "    }\n"
                + "}\n";

        CompilationUnit cu = parse(code);

        ResolvedMethodDeclaration defer =
                findMethod(cu, "defer").resolve();

        ResolvedMethodDeclaration test =
                findMethod(cu, "test").resolve();

        Map<ResolvedTypeParameterDeclaration, ResolvedType> mappings =
                new HashMap<>();

        MethodResolutionLogic.inferTypes(
                test.getParam(0).getType(),
                defer.getParam(0).getType(),
                mappings);

        ResolvedTypeParameterDeclaration tp =
                defer.getTypeParameters().get(0);

        ResolvedType inferred = mappings.get(tp);

        assertNotNull(inferred, "T was not inferred");
        assertEquals("java.lang.String", inferred.describe());
    }

    // 辅助方法只构造和解析内联源码；不会执行 Mono，也不依赖 Reactor。

    private String listCode(String formal, String actual) {
        return "import java.util.List;\n"
                + "class Example {\n"
                + "    static <T> T first(" + formal + " values) {\n"
                + "        return null;\n"
                + "    }\n"
                + "    void test(" + actual + " values) {\n"
                + "        Example.first(values);\n"
                + "    }\n"
                + "}\n";
    }

    private void assertStringLength(MethodCallExpr length) {
        assertEquals("int", length.calculateResolvedType().describe());
        assertEquals("java.lang.String", length.resolve().declaringType().getQualifiedName());
    }

    private String monoCode(String supplierType, String body) {
        return monoCode(supplierType, "", body);
    }

    private String monoCode(String supplierType, String testParameters, String body) {
        return "import java.util.function.Supplier;\n"
                + "import java.util.function.Consumer;\n"
                + "class Foo {\n"
                + "    static abstract class Mono<T> {\n"
                + "        static <T> Mono<T> defer(" + supplierType + " supplier) {\n"
                + "            return null;\n"
                + "        }\n"
                + "        final void consume(Consumer<? super T> c) {}\n"
                + "    }\n"
                + "    void test(" + testParameters + ") {\n"
                + "        " + body + "\n"
                + "    }\n"
                + "}\n";
    }

    private CompilationUnit parse(String code) {
        ParserConfiguration config = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_8)
                .setSymbolResolver(new JavaSymbolSolver(
                        new TypeSolverBuilder().withCurrentClassloader().build()));

        ParseResult<CompilationUnit> result = new JavaParser(config).parse(code);
        // 先报告语法错误，避免恢复性解析产生的 AST 被误当成类型推断失败。
        assertTrue(result.isSuccessful(), () -> "Invalid diagnostic source: " + result.getProblems());
        return result.getResult().orElseThrow(AssertionError::new);
    }

    private MethodCallExpr findCall(CompilationUnit cu, String name) {
        return cu.findAll(MethodCallExpr.class).stream()
                .filter(m -> m.getNameAsString().equals(name))
                .findFirst()
                .orElseThrow(AssertionError::new);
    }

    private MethodDeclaration findMethod(CompilationUnit cu, String name) {
        return cu.findAll(MethodDeclaration.class).stream()
                .filter(m -> m.getNameAsString().equals(name))
                .findFirst()
                .orElseThrow(AssertionError::new);
    }

    private void assertCallType(String code, String methodName, String expected) {
        CompilationUnit cu = parse(code);
        MethodCallExpr call = findCall(cu, methodName);

        assertEquals(expected, call.calculateResolvedType().describe());
    }

    private void assertLambdaParameterType(String code, String expected) {
        CompilationUnit cu = parse(code);
        NameExpr parameterUsage = cu.findAll(NameExpr.class).stream()
                .filter(n -> n.getNameAsString().equals("s"))
                .findFirst()
                .orElseThrow(AssertionError::new);

        assertEquals(expected, parameterUsage.calculateResolvedType().describe());
    }
}

