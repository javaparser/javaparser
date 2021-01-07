package com.github.javaparser.symbolsolver.resolution;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StringProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class InstanceOfTest {

    protected final TypeSolver typeSolver = new ReflectionTypeSolver();

    /**
     * Locations:
     * - Local variables
     * - If conditionals
     * <p>
     * - Usage after declaration
     * - Usage before declaration
     * <p>
     * Simple:
     * - A && B    Resolves     instanceof String s && s
     * - A || B    Not          instanceof String s || s
     * <p>
     * Negated:
     * - !A && B   Not
     * <p>
     * If/Else If/Else Blocks
     * - if(A) { Resolves }
     * - if(!A) { Not }
     * <p>
     * - if() {} else if (A) { Resolves }
     * - if() {} else if (!A) { Not }
     */
    protected final String sourceCode = "" +
            "import java.util.List;\n" +
            "\n" +
            "class X {\n" +
            "\n" +
            "    public void localVariable_shouldNotResolve() {\n" +
            "        String obj = \"abc\";\n" +
            "        boolean condition = obj instanceof String s;\n" +
            "        boolean result = s.contains(\"fails - not in scope\");\n" +
            "    }\n" +
            "\n" +
            "    public void localVariable_shouldNotResolve_usageFollowsDeclaration_shouldNotResolve() {\n" +
            "        String obj = \"abc\";\n" +
            "        boolean condition = obj instanceof String s;\n" +
            "        boolean result;\n" +
            "        result = s.contains(\"fails - not in scope\");\n" +
            "    }\n" +
            "\n" +
            "    public void localVariable_shouldNotResolve_usagePreceedsDeclaration_shouldNotResolve() {\n" +
            "        String obj = \"abc\";\n" +
            "        boolean result;\n" +
            "        result = s.contains(\"fails - not in scope\");\n" +
            "        boolean condition = obj instanceof String s;\n" +
            "    }\n" +
            "\n" +
            "    public void localVariable_shouldNotResolve_logicalAnd_shouldResolve() {\n" +
            "        String obj = \"abc\";\n" +
            "        boolean condition = obj instanceof String s && s.contains(\"in scope\");\n" +
            "    }\n" +
            "\n" +
            "    public void localVariable_shouldNotResolve_logicalOr_shouldNotResolve() {\n" +
            "        String obj = \"abc\";\n" +
            "        boolean condition = obj instanceof String s || s.contains(\"fails - not in scope\");\n" +
            "    }\n" +
            "\n" +
            "    public void if_conditional_emptyBlock_logicalAnd_shouldResolve() {\n" +
            "        String obj = \"abc\";\n" +
            "        if (obj instanceof String s && s.contains(\"in scope\")) {\n" +
            "            // Empty BlockStmt\n" +
            "        }\n" +
            "    }\n" +
            "\n" +
            "    public void if_conditional_emptyBlock_logicalOr_shouldNotResolve() {\n" +
            "        String obj = \"abc\";\n" +
            "        if (obj instanceof String s || s.contains(\"fails - not in scope\")) {\n" +
            "            // Empty BlockStmt\n" +
            "        }\n" +
            "    }\n" +
            "\n" +
            "    public void if_conditional_negated_shouldResolveToLocalVariableNotPattern() {\n" +
            "        List<Integer> s;\n" +
            "        boolean result;\n" +
            "        String obj = \"abc\";\n" +
            "        if (!(obj instanceof String s) && true) {\n" +
            "            result = s.contains(\"fails - not in scope\");\n" +
            "        }\n" +
            "    }\n" +
            "\n" +
            "    public void if_else_conditional_mixedResolveResults() {\n" +
            "        boolean result;\n" +
            "        String obj = \"abc\";\n" +
            "        if ((obj instanceof String s) && true) {\n" +
            "            result = s.contains(\"in scope\");\n" +
            "        } else {\n" +
            "            result = s.contains(\"fails - not in scope\");\n" +
            "        }\n" +
            "    }\n" +
            "\n" +
            "    public void if_else_conditional_negated_mixedResolveResults() {\n" +
            "        boolean result;\n" +
            "        String obj = \"abc\";\n" +
            "        if (!(obj instanceof String s) && true) {\n" +
            "            result = s.contains(\"fails - not in scope\");\n" +
            "        } else {\n" +
            "            result = s.contains(\"in scope\");\n" +
            "        }\n" +
            "    }\n" +
            "\n" +
            "    public void if_conditional_usageBeforeDeclaration_shouldNotResolve() {\n" +
            "        String obj = \"abc\";\n" +
            "        if(s.contains(\"fails - not in scope\") && obj instanceof String s) {\n" +
            "            // Empty BlockStmt\n" +
            "        }\n" +
            "    \n" +
            "    }\n" +
            "\n" +
            "    public void if_conditional_1_mixedResolveResults() {\n" +
            "        boolean result;\n" +
            "        String obj = \"abc\";\n" +
            "        if ((obj instanceof String s) && true) {\n" +
            "            result = s.contains(\"in scope\");\n" +
            "        } else {\n" +
            "            result = s.contains(\"fails - not in scope\");\n" +
            "        }\n" +
            "    }\n" +
            "\n" +
            "    public void if_conditional_negated_no_braces_on_else_mixed() {\n" +
            "        List<Integer> s;\n" +
            "        boolean result;\n" +
            "        String obj = \"abc\";\n" +
            "        if (!(obj instanceof String s) && true) {\n" +
            "            // Empty BlockStmt\n" +
            "        } else\n" +
            "            result = s.contains(\"in scope\");\n" +
            "    }\n" +
            "\n" +
            "    public void if_conditional_negated_no_braces_on_if_shouldResolveToLocalVariableNotPattern() {\n" +
            "        List<Integer> s;\n" +
            "        boolean result;\n" +
            "        String obj = \"abc\";\n" +
            "        if (!(obj instanceof String s) && true) \n" +
            "            result = s.contains(\"fails - not in scope\");\n" +
            "        \n" +
            "    }\n" +
            "\n" +
            "    public void if_conditional_OR_shouldNotResolve() {\n" +
            "        String obj = \"abc\";\n" +
            "        if(obj instanceof String s || s.contains(\"fails - not in scope\")) {\n" +
            "            // Empty BlockStmt\n" +
            "        }\n" +
            "    }\n" +
            "\n" +
            "\n" +
            "\n" +
            "\n" +
            "\n" +
            "\n" +
            "}\n";


    protected CompilationUnit compilationUnit;


    @BeforeEach
    public void setup() {
        compilationUnit = parseWithTypeSolver(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, sourceCode);
    }


    @Test
    public void givenInstanceOfPattern_usingJdk13_thenExpectException() {
        final String x = "" +
                "class X {\n" +
                "  public X() {\n" +
                "    boolean result;\n" +
                "    String obj = \"abc\";\n" +
                "    if (!(obj instanceof String s) && true) {\n" +
                "        result = s.contains(\"b\");\n" +
                "    }\n" +
                "  }\n" +
                " }\n";

        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        parserConfiguration.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_13);

        ParseResult<CompilationUnit> parseResult = new JavaParser(parserConfiguration)
                .parse(ParseStart.COMPILATION_UNIT, new StringProvider(x));

        assertEquals(1, parseResult.getProblems().size());
        assertEquals("Use of patterns with instanceof is not supported.", parseResult.getProblem(0).getMessage());
    }

    @Nested
    class VariableInBlock {

        @Test
        public void variableInBlock_shouldNotResolveOnFollowingLines() {
            MethodDeclaration methodDeclaration = getMethodByName("localVariable_shouldNotResolve_usageFollowsDeclaration_shouldNotResolve");
            final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
            assertEquals(1, methodCalls.size());

            MethodCallExpr outOfScopeMethodCall = methodCalls.get(0);

            // Expected to not be able to resolve s, as out of scope within an else block.
            assertThrows(UnsolvedSymbolException.class, () -> {
                final ResolvedMethodDeclaration resolve = outOfScopeMethodCall.resolve();
                // Note: Only printed if the above line doesn't error...
                System.out.println("resolve = " + resolve);
            });

        }

        @Test
        public void variableInBlock_mustNotResolveBeforeDeclaration() {

            MethodDeclaration methodDeclaration = getMethodByName("localVariable_shouldNotResolve_usagePreceedsDeclaration_shouldNotResolve");
            final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
            assertEquals(1, methodCalls.size());

            MethodCallExpr outOfScopeMethodCall = methodCalls.get(0);

            // Expected to not be able to resolve s, as it is declared after it is used.
            assertThrows(
                    UnsolvedSymbolException.class,
                    () -> {
                        final ResolvedMethodDeclaration resolve = outOfScopeMethodCall.resolve();
                        // Note: Only printed if the above line doesn't error...
                        System.out.println("resolve = " + resolve);
                        System.out.println("erroneously solved:: outOfScopeMethodCall = " + outOfScopeMethodCall);
                    },
                    "Error: Variable defined within a pattern expression is used before it is declared - should not be resolved, but is."
            );

        }

        @Nested
        class LogicalOperatorScope {

            @Test
            public void logicalAndShouldResolve() {
                MethodDeclaration methodDeclaration = getMethodByName("localVariable_shouldNotResolve_logicalAnd_shouldResolve");
                final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
                assertEquals(1, methodCalls.size());

                MethodCallExpr inScopeMethodCall = methodCalls.get(0);


                // Resolving the method call .contains()
                final ResolvedMethodDeclaration resolve = inScopeMethodCall.resolve();
                System.out.println("resolve.getQualifiedSignature() = " + resolve.getQualifiedSignature());

                assertEquals("java.lang.String.contains(java.lang.CharSequence)", resolve.getQualifiedSignature());
                assertEquals("boolean", resolve.getReturnType().describe());
                assertEquals("contains", resolve.getName());
                assertEquals(1, resolve.getNumberOfParams());
                assertEquals("contains(java.lang.CharSequence)", resolve.getSignature());


                // Resolving the variable `s`
                assertTrue(inScopeMethodCall.hasScope());
                final Expression expression = inScopeMethodCall.getScope().get();

                final ResolvedType resolvedType = expression.calculateResolvedType();
                assertEquals("java.lang.String", resolvedType.describe());

            }

            @Test
            public void logicalOrShouldNotResolve() {
                MethodDeclaration methodDeclaration = getMethodByName("localVariable_shouldNotResolve_logicalOr_shouldNotResolve");
                final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
                assertEquals(1, methodCalls.size());

                MethodCallExpr outOfScopeMethodCall = methodCalls.get(0);

                // Expected to not be able to resolve s, as it is on the right hand side of a logical or.
                assertThrows(
                        UnsolvedSymbolException.class,
                        () -> {
                            final ResolvedMethodDeclaration resolve = outOfScopeMethodCall.resolve();
                            // Note: Only printed if the above line doesn't error...
                            System.out.println("resolve = " + resolve);
                            System.out.println("erroneously solved:: outOfScopeMethodCall = " + outOfScopeMethodCall);
                        },
                        "Error: Variable defined within a pattern expression should not be available on the right hand side of an || operator."
                );
            }
        }
    }

    @Nested
    class IfElseIfElse {

        @Nested
        class Condition {

            @Test
            public void condition_rightBranch_logicalAndShouldResolveWithCorrectBreakdowns() {
                MethodDeclaration methodDeclaration = getMethodByName("if_conditional_emptyBlock_logicalAnd_shouldResolve");
                final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
                assertEquals(1, methodCalls.size());

                MethodCallExpr inScopeMethodCall = methodCalls.get(0);
                assertEquals("s.contains(\"in scope\")", inScopeMethodCall.toString());

                // Resolving the method call .contains()
                final ResolvedMethodDeclaration resolve = inScopeMethodCall.resolve();
                System.out.println("resolve.getQualifiedSignature() = " + resolve.getQualifiedSignature());

                assertEquals("java.lang.String.contains(java.lang.CharSequence)", resolve.getQualifiedSignature());
                assertEquals("boolean", resolve.getReturnType().describe());
                assertEquals("contains", resolve.getName());
                assertEquals(1, resolve.getNumberOfParams());
                assertEquals("contains(java.lang.CharSequence)", resolve.getSignature());


                // Resolving the variable `s`
                assertTrue(inScopeMethodCall.hasScope());
                final Expression expression = inScopeMethodCall.getScope().get();

                final ResolvedType resolvedType = expression.calculateResolvedType();
                assertEquals("java.lang.String", resolvedType.describe());


            }


            /**
             * This tests that the components on the right hand side resolve.
             * Useful when debugging (e.g. if the variable resolves, but not the method call).
             */
            @Test
            public void condition_rightBranch_nameExprResolves() {
                MethodDeclaration methodDeclaration = getMethodByName("if_conditional_emptyBlock_logicalAnd_shouldResolve");
                final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
                assertEquals(1, methodCalls.size());

                final List<BinaryExpr> binaryExprs = methodDeclaration.findAll(BinaryExpr.class);
                assertEquals(1, binaryExprs.size());

                BinaryExpr binaryExpr = binaryExprs.get(0);
                List<NameExpr> nameExprs = binaryExpr.getRight().findAll(NameExpr.class);
                assertEquals(1, nameExprs.size());

                NameExpr nameExpr = nameExprs.get(0);
                ResolvedValueDeclaration resolvedNameExpr = nameExpr.resolve();
                System.out.println(resolvedNameExpr);
            }


            /**
             * This tests that the components on the right hand side resolve.
             * Useful when debugging (e.g. if the variable resolves, but not the method call).
             */
            @Test
            public void condition_rightBranch_methodCallResolves() {
                MethodDeclaration methodDeclaration = getMethodByName("if_conditional_emptyBlock_logicalAnd_shouldResolve");
                final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
                assertEquals(1, methodCalls.size());

                final List<BinaryExpr> binaryExprs = methodDeclaration.findAll(BinaryExpr.class);
                assertEquals(1, binaryExprs.size());

                BinaryExpr binaryExpr = binaryExprs.get(0);
                List<MethodCallExpr> methodCallExprs = binaryExpr.getRight().findAll(MethodCallExpr.class);
                assertEquals(1, methodCallExprs.size());

                MethodCallExpr methodCallExpr = methodCallExprs.get(0);
                ResolvedType resolvedType = methodCallExpr.calculateResolvedType();
                System.out.println("resolvedType = " + resolvedType);

                ResolvedMethodDeclaration resolvedMethodDeclaration = methodCallExpr.resolve();
                System.out.println("resolvedMethodDeclaration = " + resolvedMethodDeclaration);
            }


            @Test
            public void condition_leftBranchMethodCall_doesNotResolve() {
                MethodDeclaration methodDeclaration = getMethodByName("if_conditional_usageBeforeDeclaration_shouldNotResolve");
                final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
                assertEquals(1, methodCalls.size());

                MethodCallExpr outOfScopeMethodCall = methodCalls.get(0);

                // Expected to not be able to resolve s, as out of scope within an else block.
                assertThrows(UnsolvedSymbolException.class, () -> {
                    final ResolvedMethodDeclaration resolve = outOfScopeMethodCall.resolve();
                    // Note: Only printed if the above line doesn't error...
                    System.out.println("resolve = " + resolve);
                });
            }
        }


        @Nested
        class IfElseIfElseBlock {

            @Test
            public void givenInstanceOfPattern_thenCorrectNumberOfMethodCalls() {
                MethodDeclaration methodDeclaration = getMethodByName("if_else_conditional_mixedResolveResults");
                final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
                assertEquals(2, methodCalls.size());

            }

            @Test
            public void givenInstanceOfPattern_whenSolvingInvalidNotInScope_thenFails() {
                MethodDeclaration methodDeclaration = getMethodByName("if_else_conditional_mixedResolveResults");
                final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
                assertEquals(2, methodCalls.size());

                MethodCallExpr inScopeMethodCall = methodCalls.get(0);
                MethodCallExpr outOfScopeMethodCall = methodCalls.get(1);

                // Expected to not be able to resolve s, as out of scope within an else block.
                assertThrows(UnsolvedSymbolException.class, () -> {
                    final ResolvedMethodDeclaration resolve = outOfScopeMethodCall.resolve();
                    // Note: Only printed if the above line doesn't error...
                    System.out.println("resolve = " + resolve);
                    System.out.println("erroneously solved:: outOfScopeMethodCall = " + outOfScopeMethodCall);
                });
            }

            @Test
            public void givenInstanceOfPattern_whenSolvingValidInScope_thenSuccessful() {
                MethodDeclaration methodDeclaration = getMethodByName("if_else_conditional_mixedResolveResults");
                final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
                assertEquals(2, methodCalls.size());

                MethodCallExpr inScopeMethodCall = methodCalls.get(0);
                MethodCallExpr outOfScopeMethodCall = methodCalls.get(1);


                // Resolving the method call .contains()
                final ResolvedMethodDeclaration resolve = inScopeMethodCall.resolve();
                System.out.println("resolve.getQualifiedSignature() = " + resolve.getQualifiedSignature());

                assertEquals("java.lang.String.contains(java.lang.CharSequence)", resolve.getQualifiedSignature());
                assertEquals("boolean", resolve.getReturnType().describe());
                assertEquals("contains", resolve.getName());
                assertEquals(1, resolve.getNumberOfParams());
                assertEquals("contains(java.lang.CharSequence)", resolve.getSignature());


                // Resolving the variable `s`
                assertTrue(inScopeMethodCall.hasScope());
                final Expression expression = inScopeMethodCall.getScope().get();

                final ResolvedType resolvedType = expression.calculateResolvedType();
                assertEquals("java.lang.String", resolvedType.describe());
            }
        }


        @Test
        public void givenInstanceOfPattern_andField_else_skipBraces_thenResolvesToPattern() {
            MethodDeclaration methodDeclaration = getMethodByName("if_conditional_negated_no_braces_on_else_mixed");
            final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
            assertEquals(1, methodCalls.size());

            MethodCallExpr methodCallExprInElse = methodCalls.get(0);

            // Resolving the method call .contains()
            final ResolvedMethodDeclaration resolve = methodCallExprInElse.resolve();
            System.out.println("resolve.getQualifiedSignature() = " + resolve.getQualifiedSignature());

            // The method call in the else block should be in scope of the pattern (String) due to the negated condition
            assertEquals("java.lang.String.contains(java.lang.CharSequence)", resolve.getQualifiedSignature());
            assertEquals("boolean", resolve.getReturnType().describe());
            assertEquals("contains", resolve.getName());
            assertEquals(1, resolve.getNumberOfParams());
            assertEquals("contains(java.lang.CharSequence)", resolve.getSignature());

        }

        @Test
        public void givenInstanceOfPattern_andField_skipBraces_thenResolvesToPattern() {
            MethodDeclaration methodDeclaration = getMethodByName("if_conditional_negated_no_braces_on_if_shouldResolveToLocalVariableNotPattern");
            final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
            assertEquals(1, methodCalls.size());

            MethodCallExpr outOfScopeMethodCall = methodCalls.get(0);

            // Resolving the method call .contains()
            final ResolvedMethodDeclaration resolve = outOfScopeMethodCall.resolve();
            System.out.println("resolve.getQualifiedSignature() = " + resolve.getQualifiedSignature());

            // Should resolve to the field (List.contains()), not the pattern expression (String.contains())
            assertEquals("java.util.List.contains(java.lang.Object)", resolve.getQualifiedSignature());
            assertEquals("boolean", resolve.getReturnType().describe());
            assertEquals("contains", resolve.getName());
            assertEquals(1, resolve.getNumberOfParams());
            assertEquals("contains(java.lang.Object)", resolve.getSignature());

        }

        @Test
        public void givenInstanceOfPattern_andField_thenResolvesToField() {
            MethodDeclaration methodDeclaration = getMethodByName("if_conditional_negated_shouldResolveToLocalVariableNotPattern");
            final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
            assertEquals(1, methodCalls.size());

            MethodCallExpr outOfScopeMethodCall = methodCalls.get(0);

            // Resolving the method call .contains()
            final ResolvedMethodDeclaration resolve = outOfScopeMethodCall.resolve();
            System.out.println("resolve.getQualifiedSignature() = " + resolve.getQualifiedSignature());

            // Should resolve to the field (List.contains()), not the pattern expression (String.contains())
            assertEquals("java.util.List.contains(java.lang.Object)", resolve.getQualifiedSignature());
            assertEquals("boolean", resolve.getReturnType().describe());
            assertEquals("contains", resolve.getName());
            assertEquals(1, resolve.getNumberOfParams());
            assertEquals("contains(java.lang.Object)", resolve.getSignature());
        }

        @Test
        public void test_shouldFail() {
            MethodDeclaration methodDeclaration = getMethodByName("if_conditional_OR_shouldNotResolve");
            final List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
            assertEquals(1, methodCalls.size());

            assertEquals(1, methodCalls.size());

            MethodCallExpr outOfScopeMethodCall = methodCalls.get(0);

            // Expected to not be able to resolve s, as out of scope within an else block.
            assertThrows(UnsolvedSymbolException.class, () -> {
                final ResolvedMethodDeclaration resolve = outOfScopeMethodCall.resolve();
                // Note: Only printed if the above line doesn't error...
                System.out.println("resolve = " + resolve);
            });
        }

    }


    @Nested
    class Simpler {

        @Test
        public void test() {
            MethodDeclaration methodDeclaration = getMethodByName("localVariable_shouldNotResolve");

            List<NameExpr> nameExprs = methodDeclaration.findAll(NameExpr.class);
            System.out.println("nameExprs = " + nameExprs);

            assertEquals(2, nameExprs.size());

            NameExpr nameExpr = nameExprs.get(0);
            ResolvedValueDeclaration resolvedNameExpr = nameExpr.resolve();
            ResolvedType resolvedNameExprType = nameExpr.calculateResolvedType();

            System.out.println("resolvedNameExpr = " + resolvedNameExpr);
            System.out.println("resolvedNameExprType = " + resolvedNameExprType);

        }
    }

    private MethodDeclaration getMethodByName(String name) {
        return compilationUnit
                .findAll(MethodDeclaration.class)
                .stream()
                .filter(methodDeclaration -> methodDeclaration.getNameAsString().equals(name))
                .findFirst()
                .orElseThrow(RuntimeException::new);
    }

    private CompilationUnit parseWithTypeSolver(String code) {
        return parseWithTypeSolver(null, code);
    }

    private CompilationUnit parseWithTypeSolver(ParserConfiguration.LanguageLevel languageLevel, String code) {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));

        if (languageLevel != null) {
            parserConfiguration.setLanguageLevel(languageLevel);
        }

        return new JavaParser(parserConfiguration)
                .parse(ParseStart.COMPILATION_UNIT, new StringProvider(code))
                .getResult().get();
    }


}
