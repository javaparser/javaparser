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

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.List;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Regression tests for GitHub issue #2684.
 *
 * <p>When iterating all {@link NameExpr} nodes in a compilation unit and calling
 * {@link NameExpr#resolve()}, the symbol solver was throwing a cryptic
 * {@link UnsolvedSymbolException} for names that denote types rather than values
 * (e.g., {@code System} in {@code System.out.println()}).
 *
 * <p>Root cause: per JLS §6.5, a simple name is contextually ambiguous — it may denote
 * either a <em>value</em> (variable, field, parameter) or a <em>type</em> (class,
 * interface, enum). The symbol solver's {@code solveSymbol} only searches value
 * declarations and never checked the implicit {@code java.lang} package.
 *
 * <p>Fix: {@link NameExpr} now implements {@code Resolvable<ResolvedDeclaration>} instead
 * of {@code Resolvable<ResolvedValueDeclaration>}. The {@link NameExpr#resolve()} method
 * returns the common supertype {@link ResolvedDeclaration} and a fallback to
 * {@code solveType} was added in {@link JavaSymbolSolver#resolveDeclaration} so that
 * type-denoting names are resolved to a {@link ResolvedTypeDeclaration} rather than
 * throwing. Callers use {@link ResolvedDeclaration#isType()} to branch on the result kind.
 */
class Issue2684Test {

    @BeforeEach
    void setUp() {
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        StaticJavaParser.setConfiguration(config);
    }

    @AfterEach
    void tearDown() {
        // Reset to a clean configuration so this test does not affect other test classes.
        StaticJavaParser.setConfiguration(new ParserConfiguration());
    }

    // -------------------------------------------------------------------------
    // Core regression: resolve() on a type-qualifier NameExpr must succeed
    // -------------------------------------------------------------------------

    /**
     * {@code System} in {@code System.out.println()} is a type name (java.lang.System).
     * Before the fix, {@code resolve()} threw a cryptic exception. After the fix it must
     * succeed and return a {@link ResolvedTypeDeclaration} flagged with {@code isType()}.
     */
    @Test
    void resolve_onJavaLangTypeQualifier_returnsTypeDeclaration() {
        CompilationUnit cu = StaticJavaParser.parse(
                "class Test { void m() { System.out.println(\"hello\"); } }");

        NameExpr systemExpr = findNameExpr(cu, "System");

        // Before the fix this threw — it must now succeed.
        ResolvedDeclaration decl = assertDoesNotThrow(systemExpr::resolve);

        // The result must be flagged as a type so callers can distinguish it from a value.
        assertTrue(decl.isType(),
                "Expected isType() == true for a type-qualifier NameExpr, but got: " + decl);
        assertEquals("java.lang.System", decl.asType().getQualifiedName());
    }

    /**
     * {@code String} is another implicitly imported java.lang type commonly seen as a
     * static-method qualifier.
     *
     * <p>Note: a cast expression like {@code (String) x} uses a {@code ClassOrInterfaceType}
     * node, not a {@code NameExpr}. {@code String.valueOf(42)} produces the required
     * {@code NameExpr}.
     */
    @Test
    void resolve_onJavaLangStringQualifier_returnsTypeDeclaration() {
        CompilationUnit cu = StaticJavaParser.parse(
                "class Test { void m() { String.valueOf(42); } }");

        NameExpr stringExpr = findNameExpr(cu, "String");
        ResolvedDeclaration decl = assertDoesNotThrow(stringExpr::resolve);

        assertTrue(decl.isType());
        assertEquals("java.lang.String", decl.asType().getQualifiedName());
    }

    /**
     * A user-defined class used as a qualifier must also be resolvable — not only
     * java.lang classes benefit from the type-fallback path.
     */
    @Test
    void resolve_onUserDefinedClassQualifier_returnsTypeDeclaration() {
        CompilationUnit cu = StaticJavaParser.parse(
                "class Foo { static int VALUE = 42; }"
                        + "class Test { void m() { int x = Foo.VALUE; } }");

        NameExpr fooExpr = findNameExpr(cu, "Foo");
        ResolvedDeclaration decl = assertDoesNotThrow(fooExpr::resolve);

        assertTrue(decl.isType());
        assertEquals("Foo", decl.asType().getName());
    }

    // -------------------------------------------------------------------------
    // Value-denoting names: resolve() must still return ResolvedValueDeclaration
    // -------------------------------------------------------------------------

    /**
     * {@code resolve()} on a local variable must still return a {@link ResolvedValueDeclaration}
     * at runtime, with {@code isType() == false}. The breaking change must not regress
     * ordinary value resolution.
     */
    @Test
    void resolve_onLocalVariable_returnsValueDeclaration() {
        CompilationUnit cu = StaticJavaParser.parse(
                "class Test { void m() { int count = 0; int x = count + 1; } }");

        NameExpr countExpr = findNameExpr(cu, "count");
        ResolvedDeclaration decl = assertDoesNotThrow(countExpr::resolve);

        assertFalse(decl.isType(),
                "Expected isType() == false for a value-denoting NameExpr");
        assertInstanceOf(ResolvedValueDeclaration.class, decl);
        assertEquals("int", ((ResolvedValueDeclaration) decl).getType().describe());
    }

    /**
     * {@code resolve()} on a method parameter must return a {@link ResolvedValueDeclaration}.
     */
    @Test
    void resolve_onMethodParameter_returnsValueDeclaration() {
        CompilationUnit cu = StaticJavaParser.parse(
                "class Test { void m(String name) { System.out.println(name); } }");

        NameExpr nameExpr = findNameExpr(cu, "name");
        ResolvedDeclaration decl = assertDoesNotThrow(nameExpr::resolve);

        assertFalse(decl.isType());
        assertInstanceOf(ResolvedValueDeclaration.class, decl);
        assertEquals(
                "java.lang.String",
                ((ResolvedValueDeclaration) decl).getType().asReferenceType().getQualifiedName());
    }

    // -------------------------------------------------------------------------
    // resolveDeclaration with an explicit target class
    // -------------------------------------------------------------------------

    /**
     * Callers that invoke {@link JavaSymbolSolver#resolveDeclaration} directly with
     * {@link ResolvedTypeDeclaration} as the target class must also benefit from the
     * type-fallback path introduced by the fix.
     */
    @Test
    void resolveDeclaration_asTypeDeclaration_resolvesJavaLangSystem() {
        CompilationUnit cu = StaticJavaParser.parse(
                "class Test { void m() { System.out.println(\"hello\"); } }");

        NameExpr systemExpr = findNameExpr(cu, "System");
        JavaSymbolSolver solver =
                (JavaSymbolSolver) cu.getData(com.github.javaparser.ast.Node.SYMBOL_RESOLVER_KEY);

        ResolvedTypeDeclaration typeDecl =
                solver.resolveDeclaration(systemExpr, ResolvedTypeDeclaration.class);

        assertEquals("java.lang.System", typeDecl.getQualifiedName());
    }

    // -------------------------------------------------------------------------
    // Failure case: truly unknown symbols must still throw
    // -------------------------------------------------------------------------

    /**
     * A name that cannot be resolved as either a value or a type must still throw
     * {@link UnsolvedSymbolException}. The fallback must not suppress genuine failures.
     */
    @Test
    void resolve_onUnknownSymbol_throwsUnsolvedSymbolException() {
        CompilationUnit cu = StaticJavaParser.parse(
                "class Test { void m() { unknownSymbol; } }");

        NameExpr unknown = findNameExpr(cu, "unknownSymbol");

        assertThrows(UnsolvedSymbolException.class, unknown::resolve);
    }

    // -------------------------------------------------------------------------
    // calculateResolvedType() consistency
    // -------------------------------------------------------------------------

    /**
     * {@code calculateResolvedType()} must agree with {@code resolve().asType().getQualifiedName()}
     * for type-denoting names.
     */
    @Test
    void calculateResolvedType_andResolve_agreeOnTypeName() {
        CompilationUnit cu = StaticJavaParser.parse(
                "class Test { void m() { System.out.println(\"hello\"); } }");

        NameExpr systemExpr = findNameExpr(cu, "System");

        String viaCalculate = systemExpr.calculateResolvedType().describe();
        String viaResolve   = systemExpr.resolve().asType().getQualifiedName();

        assertEquals(viaCalculate, viaResolve,
                "calculateResolvedType() and resolve().asType() must agree on the type name");
    }

    // -------------------------------------------------------------------------
    // Integration: the exact scenario from issue #2684
    // -------------------------------------------------------------------------

    /**
     * Reproduces the exact usage pattern from issue #2684: iterate all {@link NameExpr}
     * nodes in a compilation unit and call {@code resolve()} on each. No unexpected
     * exception (anything other than {@link UnsolvedSymbolException}) must be thrown.
     */
    @Test
    void resolve_onAllNameExprs_neverThrowsUnexpectedException() {
        CompilationUnit cu = StaticJavaParser.parse("package test;\n"
                + "class HelloWorld {\n"
                + "    private void greet() throws java.io.IOException {\n"
                + "        System.out.println(\"Hello World\");\n"
                + "    }\n"
                + "}");

        List<NameExpr> exprs = cu.findAll(NameExpr.class);
        assertFalse(exprs.isEmpty(), "Expected at least one NameExpr in the test class");

        for (NameExpr expr : exprs) {
            try {
                expr.resolve();
            } catch (UnsolvedSymbolException e) {
                // Acceptable: some names may be genuinely unresolvable (e.g., external
                // references not on the classpath). Any other exception type is a bug.
            }
        }
    }

    // -------------------------------------------------------------------------
    // Helper
    // -------------------------------------------------------------------------

    /**
     * Finds the last {@link NameExpr} in the compilation unit whose identifier matches
     * {@code name}. Using the last occurrence targets the <em>use site</em> rather than
     * a declaration site (e.g., the class name in its own declaration header).
     */
    private NameExpr findNameExpr(CompilationUnit cu, String name) {
        return cu.findAll(NameExpr.class).stream()
                .filter(e -> e.getNameAsString().equals(name))
                .reduce((first, second) -> second) // last = use site
                .orElseThrow(() -> new AssertionError("No NameExpr named '" + name + "' found"));
    }
}
