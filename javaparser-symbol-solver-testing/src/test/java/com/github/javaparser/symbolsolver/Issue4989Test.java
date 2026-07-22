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

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Reproducer for <a href="https://github.com/javaparser/javaparser/issues/4989">#4989</a>.
 *
 * <p>Resolving {@code methodCallExpr.resolve().getQualifiedSignature()} on a stream pipeline that
 * uses {@code X.class::isInstance} / {@code X.class::cast} followed by an instance method reference
 * ({@code this::convert}) fails, because {@code Class::cast} does not refine the stream element
 * type from the source type to the cast target type.
 *
 * <pre>{@code
 * contentBlocks.stream()
 *     .filter(ToolUseBlock.class::isInstance)
 *     .map(ToolUseBlock.class::cast)
 *     .map(this::convertToolUseBlockToToolCall)
 *     .collect(Collectors.toList());
 * }</pre>
 */
public class Issue4989Test extends AbstractResolutionTest {

    private static final String CODE = ""
            + "import java.util.List;\n"
            + "import java.util.stream.Collectors;\n"
            + "\n"
            + "public class ChatCompletionsResponseBuilder {\n"
            + "\n"
            + "    interface ContentBlock {}\n"
            + "\n"
            + "    static class ToolUseBlock implements ContentBlock {\n"
            + "        String id;\n"
            + "        String name;\n"
            + "        String input;\n"
            + "    }\n"
            + "\n"
            + "    static class ToolCall {\n"
            + "        ToolCall(String id, String name, String input) {}\n"
            + "    }\n"
            + "\n"
            + "    public List<ToolCall> extractToolCalls(List<ContentBlock> contentBlocks) {\n"
            + "        return contentBlocks.stream()\n"
            + "                .filter(ToolUseBlock.class::isInstance)\n"
            + "                .map(ToolUseBlock.class::cast)\n"
            + "                .map(this::convertToolUseBlockToToolCall)\n"
            + "                .collect(Collectors.toList());\n"
            + "    }\n"
            + "\n"
            + "    private ToolCall convertToolUseBlockToToolCall(ToolUseBlock toolUse) {\n"
            + "        return new ToolCall(toolUse.id, toolUse.name, toolUse.input);\n"
            + "    }\n"
            + "}\n";

    @BeforeEach
    void setup() {
        ParserConfiguration config =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);
    }

    /**
     * {@code X.class::cast} used as a stream mapper should yield {@code Stream<X>}, not the
     * pre-cast element type.
     */
    @Test
    void mapClassCastShouldRefineStreamElementType() {
        String code = ""
                + "import java.util.List;\n"
                + "import java.util.stream.Stream;\n"
                + "public class A {\n"
                + "  interface Base {}\n"
                + "  static class Sub implements Base {}\n"
                + "  public Stream<Sub> f(List<Base> list) {\n"
                + "    return list.stream().map(Sub.class::cast);\n"
                + "  }\n"
                + "}\n";

        CompilationUnit cu = StaticJavaParser.parse(code);
        MethodCallExpr mapCall = cu.findAll(MethodCallExpr.class).stream()
                .filter(m -> m.getNameAsString().equals("map"))
                .findFirst()
                .orElseThrow(AssertionError::new);

        assertEquals(
                "java.util.stream.Stream<A.Sub>",
                mapCall.calculateResolvedType().describe());
    }

    /**
     * Direct resolution of the instance method reference after {@code class::cast}.
     * This is the failure reported in the issue:
     * {@code Unable to resolve method reference this::convertToolUseBlockToToolCall ...}
     */
    @Test
    void resolveInstanceMethodReferenceAfterClassCast() {
        CompilationUnit cu = StaticJavaParser.parse(CODE);

        MethodReferenceExpr thisConvert = cu.findAll(MethodReferenceExpr.class).stream()
                .filter(m -> m.toString().equals("this::convertToolUseBlockToToolCall"))
                .findFirst()
                .orElseThrow(AssertionError::new);

        ResolvedMethodDeclaration resolved =
                assertDoesNotThrow(thisConvert::resolve, "Failed to resolve this::convertToolUseBlockToToolCall");
        assertEquals(
                "ChatCompletionsResponseBuilder.convertToolUseBlockToToolCall("
                        + "ChatCompletionsResponseBuilder.ToolUseBlock)",
                resolved.getQualifiedSignature());
    }

    /**
     * Exactly the API used by the reporter:
     * {@code methodCallExpr.resolve().getQualifiedSignature()} on every call in the pipeline,
     * including {@code collect(...)} whose scope contains the failing method reference.
     */
    @Test
    void resolveAllMethodCallsInStreamPipeline() {
        CompilationUnit cu = StaticJavaParser.parse(CODE);

        for (MethodCallExpr mce : cu.findAll(MethodCallExpr.class)) {
            ResolvedMethodDeclaration resolved = assertDoesNotThrow(mce::resolve, () -> "Failed to resolve: " + mce);
            assertDoesNotThrow(resolved::getQualifiedSignature, () -> "Failed getQualifiedSignature for: " + mce);
        }
    }

    /**
     * Control case: the same instance method reference works when the stream element type is
     * already the expected parameter type (no {@code class::cast} involved).
     */
    @Test
    void baselineInstanceMethodReferenceWithoutCastWorks() {
        String code = ""
                + "import java.util.List;\n"
                + "import java.util.stream.Collectors;\n"
                + "public class A {\n"
                + "  static class Sub { String v; }\n"
                + "  static class Out { Out(String v) {} }\n"
                + "  public List<Out> f(List<Sub> list) {\n"
                + "    return list.stream().map(this::convert).collect(Collectors.toList());\n"
                + "  }\n"
                + "  private Out convert(Sub s) { return new Out(s.v); }\n"
                + "}\n";

        CompilationUnit cu = StaticJavaParser.parse(code);

        MethodReferenceExpr mre = cu.findFirst(MethodReferenceExpr.class).orElseThrow(AssertionError::new);
        assertEquals("A.convert(A.Sub)", mre.resolve().getQualifiedSignature());

        MethodCallExpr collect = cu.findAll(MethodCallExpr.class).stream()
                .filter(m -> m.getNameAsString().equals("collect"))
                .findFirst()
                .orElseThrow(AssertionError::new);
        assertEquals(
                "java.util.stream.Stream.collect(java.util.stream.Collector<? super T, A, R>)",
                collect.resolve().getQualifiedSignature());
        assertEquals("java.util.List<A.Out>", collect.calculateResolvedType().describe());
    }
}
