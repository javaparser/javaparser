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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.MethodAmbiguityException;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.List;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;

/**
 * Regression tests for issue 4917: an implicitly typed lambda parameter must remain resolvable
 * when passed to a statically imported helper inside the lambda body.
 */
class Issue4917Test extends AbstractSymbolResolutionTest {

    private static final String FIXTURE = "issue4917.Fixture.";
    private static final String TASK = FIXTURE + "Task";
    private static final String QUERY = FIXTURE + "Query<" + TASK + ">";
    private static final String PAGE_REQUEST = FIXTURE + "PageRequest<" + TASK + ">";
    private static final String STREAM = "java.util.stream.Stream<" + TASK + ">";
    private static final String STATIC_CALL =
            "grid.setItems(query -> taskService.list(toSpringPageRequest(query)).stream());";

    private CombinedTypeSolver typeSolver;
    private JavaParser parser;

    @BeforeEach
    void setUp() {
        typeSolver = new CombinedTypeSolver(
                new ReflectionTypeSolver(),
                new JavaParserTypeSolver(
                        adaptPath("src/test/resources/issue4917"),
                        new ParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_8)));
        parser = new JavaParser(new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_8)
                .setSymbolResolver(new JavaSymbolSolver(typeSolver)));
    }

    @Test
    void qualifiedHelperCallIsTheBaseline() {
        CompilationUnit cu =
                parse("", "grid.setItems(query -> taskService.list(Helpers.toSpringPageRequest(query)).stream());");

        assertPipeline(cu, FIXTURE + "Helpers.toSpringPageRequest(" + QUERY + ")", PAGE_REQUEST);
    }

    @Test
    void directlyImportedHelperResolves() {
        CompilationUnit cu = parse(staticImport("Helpers"), STATIC_CALL);

        assertPipeline(cu, FIXTURE + "Helpers.toSpringPageRequest(" + QUERY + ")", PAGE_REQUEST);
    }

    @Test
    void overloadedStaticHelperSelectsTheQueryOverload() {
        CompilationUnit cu = parse(staticImport("OverloadedHelpers"), STATIC_CALL);

        assertPipeline(cu, FIXTURE + "OverloadedHelpers.toSpringPageRequest(" + QUERY + ")", PAGE_REQUEST);
    }

    @Test
    void wildcardStaticImportResolves() {
        CompilationUnit cu = parse("import static issue4917.Fixture.Helpers.*;\n", STATIC_CALL);

        assertPipeline(cu, FIXTURE + "Helpers.toSpringPageRequest(" + QUERY + ")", PAGE_REQUEST);
    }

    @ParameterizedTest
    @ValueSource(booleans = {false, true})
    void genericStaticHelperInfersItsTypeArgumentFromTheLambdaParameter(boolean onDemand) {
        CompilationUnit cu = parse(importHelper("GenericHelpers", onDemand), STATIC_CALL);

        assertPipeline(
                cu,
                FIXTURE + "GenericHelpers.toSpringPageRequest(" + FIXTURE + "Query<T>)",
                FIXTURE + "PageRequest<T>");

        MethodUsage usage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call(cu, "toSpringPageRequest"));
        assertEquals(QUERY, usage.getParamType(0).describe());
        assertEquals(PAGE_REQUEST, usage.returnType().describe());
    }

    @Test
    void qualifiedGenericHelperInfersItsTypeArgumentFromTheLambdaParameter() {
        CompilationUnit cu = parse(
                "", "grid.setItems(query -> taskService.list(GenericHelpers.toSpringPageRequest(query)).stream());");

        assertPipeline(
                cu,
                FIXTURE + "GenericHelpers.toSpringPageRequest(" + FIXTURE + "Query<T>)",
                FIXTURE + "PageRequest<T>");
    }

    @Test
    void resolvesTheOuterCallBeforeTheLambdaBody() {
        CompilationUnit cu = parse(staticImport("Helpers"), STATIC_CALL);
        assertCall(cu, "setItems", FIXTURE + "Grid.setItems(" + FIXTURE + "FetchCallback<T>)", "void");
        assertPipeline(cu, FIXTURE + "Helpers.toSpringPageRequest(" + QUERY + ")", PAGE_REQUEST);
    }

    @ParameterizedTest
    @CsvSource({"Helpers, false", "Helpers, true", "GenericHelpers, false", "GenericHelpers, true"})
    void nestedLambdaKeepsTheInnerParameterAndCapturedOuterParameterDistinct(String helperClass, boolean onDemand) {
        CompilationUnit cu = parse(
                importHelper(helperClass, onDemand),
                "grid.setItems(query -> taskService.list(toSpringPageRequest(query)).stream()"
                        + ".filter(task -> task.matches(toSpringPageRequest(query))));");

        assertEquals(2, cu.findAll(LambdaExpr.class).size());
        assertEquals(2, helperCalls(cu).size());
        if (helperClass.equals("GenericHelpers")) {
            assertPipeline(
                    cu,
                    FIXTURE + "GenericHelpers.toSpringPageRequest(" + FIXTURE + "Query<T>)",
                    FIXTURE + "PageRequest<T>");
        } else {
            assertPipeline(cu, FIXTURE + "Helpers.toSpringPageRequest(" + QUERY + ")", PAGE_REQUEST);
        }
        assertLambdaParameter(cu, "task", TASK);
        assertCall(cu, "matches", FIXTURE + "Task.matches(" + PAGE_REQUEST + ")", "boolean");
        assertCall(cu, "filter", "java.util.stream.Stream.filter(java.util.function.Predicate<? super T>)", STREAM);
    }

    @ParameterizedTest
    @CsvSource({"StringHelpers, Helpers", "Helpers, StringHelpers", "ObjectHelpers, Helpers", "Helpers, ObjectHelpers"})
    void sameNameImportedFromTwoClassesSelectsTheApplicableOverload(String first, String second) {
        CompilationUnit cu = parse(staticWildcardImport(first) + staticWildcardImport(second), STATIC_CALL);

        assertPipeline(cu, FIXTURE + "Helpers.toSpringPageRequest(" + QUERY + ")", PAGE_REQUEST);
    }

    @ParameterizedTest
    @CsvSource({"StringHelpers, Helpers", "Helpers, StringHelpers", "ObjectHelpers, Helpers", "Helpers, ObjectHelpers"})
    void sameNameSingleImportsSelectTheApplicableOverload(String first, String second) {
        CompilationUnit cu = parse(staticImport(first) + staticImport(second), STATIC_CALL);

        assertPipeline(cu, FIXTURE + "Helpers.toSpringPageRequest(" + QUERY + ")", PAGE_REQUEST);
    }

    @ParameterizedTest
    @CsvSource({
        "Helpers, DuplicateHelpers, false",
        "DuplicateHelpers, Helpers, false",
        "Helpers, DuplicateHelpers, true",
        "DuplicateHelpers, Helpers, true"
    })
    void sameNameImportedFromTwoClassesReportsAmbiguity(String first, String second, boolean onDemand) {
        // Deliberately ambiguous Java: two static imports contribute the same applicable signature.
        String imports = importHelper(first, onDemand) + importHelper(second, onDemand);
        CompilationUnit cu = parse(imports, STATIC_CALL);
        MethodCallExpr helper = call(cu, "toSpringPageRequest");

        assertThrows(MethodAmbiguityException.class, helper::resolve);
        // Check the type-calculation API independently, without any cached resolution of the call.
        MethodCallExpr freshHelper = call(parse(imports, STATIC_CALL), "toSpringPageRequest");
        assertThrows(MethodAmbiguityException.class, freshHelper::calculateResolvedType);
    }

    @ParameterizedTest
    @CsvSource({"Helpers, Helpers", "Helpers, InheritedHelpers", "InheritedHelpers, Helpers"})
    void importingTheSameDeclarationTwiceIsNotAmbiguous(String first, String second) {
        CompilationUnit cu = parse(staticWildcardImport(first) + staticWildcardImport(second), STATIC_CALL);
        assertPipeline(cu, FIXTURE + "Helpers.toSpringPageRequest(" + QUERY + ")", PAGE_REQUEST);
    }

    @ParameterizedTest
    @CsvSource({"Helpers, HidingHelpers", "HidingHelpers, Helpers"})
    void aStaticMethodHidingItsAncestorIsPreferred(String first, String second) {
        CompilationUnit cu = parse(staticWildcardImport(first) + staticWildcardImport(second), STATIC_CALL);
        assertPipeline(cu, FIXTURE + "HidingHelpers.toSpringPageRequest(" + QUERY + ")", PAGE_REQUEST);
    }

    @ParameterizedTest
    @ValueSource(booleans = {false, true})
    void singleStaticImportShadowsAMoreSpecificOnDemandImport(boolean reverseOrder) {
        String single = staticImport("ObjectHelpers");
        String wildcard = staticWildcardImport("Helpers");
        CompilationUnit cu = parse(reverseOrder ? wildcard + single : single + wildcard, STATIC_CALL);
        assertPipeline(cu, FIXTURE + "ObjectHelpers.toSpringPageRequest(java.lang.Object)", PAGE_REQUEST);
    }

    @Test
    void inapplicableSingleStaticImportDoesNotFallBackToOnDemandImports() {
        CompilationUnit cu = parse(staticWildcardImport("Helpers") + staticImport("StringHelpers"), STATIC_CALL);
        assertLambdaParameter(cu, "query", QUERY);
        assertThrows(UnsolvedSymbolException.class, call(cu, "toSpringPageRequest")::resolve);
    }

    private CompilationUnit parse(String imports, String statement) {
        String source = "package issue4917.client;\n"
                + imports
                + "import issue4917.Fixture.*;\n"
                + "class Client {\n"
                + "    Grid<Task> grid;\n"
                + "    TaskService taskService;\n"
                + "    void configure() {\n"
                + "        " + statement + "\n"
                + "    }\n"
                + "}\n";
        ParseResult<CompilationUnit> result = parser.parse(source);
        assertTrue(result.isSuccessful(), () -> result.getProblems().toString());
        return result.getResult().orElseThrow(AssertionError::new);
    }

    private String staticImport(String helperClass) {
        return "import static " + FIXTURE + helperClass + ".toSpringPageRequest;\n";
    }

    private String staticWildcardImport(String helperClass) {
        return "import static " + FIXTURE + helperClass + ".*;\n";
    }

    private String importHelper(String helperClass, boolean onDemand) {
        return onDemand ? staticWildcardImport(helperClass) : staticImport(helperClass);
    }

    private void assertPipeline(CompilationUnit cu, String helperSignature, String declaredHelperReturnType) {
        List<MethodCallExpr> helpers = helperCalls(cu);
        assertFalse(helpers.isEmpty());
        for (MethodCallExpr helper : helpers) {
            // Resolve the reported failing call before explicitly requesting any lambda parameter type.
            ResolvedMethodDeclaration declaration = helper.resolve();
            assertEquals(helperSignature, declaration.getQualifiedSignature());
            assertTrue(declaration.isStatic());
            assertEquals(declaredHelperReturnType, declaration.getReturnType().describe());
            assertEquals(QUERY, helper.getArgument(0).calculateResolvedType().describe());
            assertEquals(PAGE_REQUEST, helper.calculateResolvedType().describe());
        }

        assertLambdaParameter(cu, "query", QUERY);
        assertCall(cu, "list", FIXTURE + "TaskService.list(" + PAGE_REQUEST + ")", "java.util.List<" + TASK + ">");
        assertCall(cu, "stream", "java.util.Collection.stream()", STREAM);
        assertCall(cu, "setItems", FIXTURE + "Grid.setItems(" + FIXTURE + "FetchCallback<T>)", "void");
        assertEquals(
                FIXTURE + "FetchCallback<" + TASK + ">",
                call(cu, "setItems").getArgument(0).calculateResolvedType().describe());
    }

    private void assertLambdaParameter(CompilationUnit cu, String name, String expectedType) {
        LambdaExpr lambda = cu.findFirst(
                        LambdaExpr.class,
                        expr -> expr.getParameter(0).getNameAsString().equals(name))
                .orElseThrow(AssertionError::new);
        assertTrue(lambda.getParameter(0).getType().isUnknownType());
        assertEquals(expectedType, lambda.getParameter(0).resolve().describeType());

        List<NameExpr> uses =
                cu.findAll(NameExpr.class, expr -> expr.getNameAsString().equals(name));
        assertFalse(uses.isEmpty());
        for (NameExpr use : uses) {
            assertEquals(expectedType, use.calculateResolvedType().describe());
        }
    }

    private List<MethodCallExpr> helperCalls(CompilationUnit cu) {
        return cu.findAll(MethodCallExpr.class, expr -> expr.getNameAsString().equals("toSpringPageRequest"));
    }

    private void assertCall(CompilationUnit cu, String name, String signature, String resultType) {
        MethodCallExpr call = call(cu, name);
        assertEquals(signature, call.resolve().getQualifiedSignature());
        assertEquals(resultType, call.calculateResolvedType().describe());
    }

    private MethodCallExpr call(CompilationUnit cu, String name) {
        return cu.findFirst(MethodCallExpr.class, expr -> expr.getNameAsString().equals(name))
                .orElseThrow(() -> new AssertionError("Missing call: " + name));
    }
}
