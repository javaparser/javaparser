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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.List;
import java.util.stream.Collectors;
import org.junit.jupiter.api.*;

class JavaParserTypeDeclarationAdapterTest extends AbstractResolutionTest {

    @BeforeAll
    static void setUpBeforeClass() throws Exception {}

    @AfterAll
    static void tearDownAfterClass() throws Exception {}

    @BeforeEach
    void setUp() throws Exception {}

    @AfterEach
    void tearDownAfterEach() throws Exception {}

    @Test
    void issue3214() {
        String code = "public interface Foo {\n"
                + "	    interface Bar {}\n"
                + "	}\n"
                + "\n"
                + "	public interface Bar {\n"
                + "	    void show();\n"
                + "	}\n"
                + "\n"
                + "	public class Test implements Foo.Bar {\n"
                + "	    private Bar bar;\n"
                + "	    private void m() {\n"
                + "	        bar.show();\n"
                + "	    }\n"
                + "	}";

        JavaParserAdapter parser = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()));
        CompilationUnit cu = parser.parse(code);

        MethodCallExpr mce = cu.findAll(MethodCallExpr.class).get(0);

        assertEquals("Bar.show()", mce.resolve().getQualifiedSignature());
    }

    @Test
    void issue3550() {
        // A class implementing an interface should be able to reference that interface's nested
        // types by relative name (e.g. "Sub.Test" instead of the fully-qualified "Base.Sub.Test").
        // Previously, the symbol solver only searched for the innermost part of the name ("Test")
        // in ancestors, ignoring intermediate segments, which caused an UnsolvedSymbolException.
        String code = "interface Base {\n"
                + "    interface Sub {\n"
                + "        class Test {}\n"
                + "    }\n"
                + "}\n"
                + "class Default implements Base {\n"
                + "    Base.Sub.Test x1;\n" // fully-qualified path — always worked
                + "    Sub.Test x2;\n" // relative path — was throwing UnsolvedSymbolException
                + "}";

        final JavaSymbolSolver solver = new JavaSymbolSolver(new ReflectionTypeSolver(false));
        StaticJavaParser.getParserConfiguration().setSymbolResolver(solver);
        final CompilationUnit compilationUnit = StaticJavaParser.parse(code);

        // Both fields must resolve to the same qualified type name.
        final List<String> fieldTypes = compilationUnit.findAll(FieldDeclaration.class).stream()
                .map(fd -> fd.getVariable(0).getType().resolve().describe())
                .collect(Collectors.toList());

        assertEquals(2, fieldTypes.size());
        fieldTypes.forEach(type -> assertEquals("Base.Sub.Test", type));
    }

    @Test
    void issue3946() {

        String code = "interface Activity {\n"
                + "class Timestamps {}\n"
                + "  Timestamps getTimestamps();\n"
                + "}\n"
                + "interface RichPresence extends Activity {}\n"
                + "  class ActivityImpl implements Activity {\n"
                + "    RichPresence.Timestamps timestamps;\n"
                + "    @Override\n"
                + "	   public RichPresence.Timestamps getTimestamps() { return timestamps; }\n"
                + "    }\n"
                + "class RichPresenceImpl extends ActivityImpl implements RichPresence { }";

        final JavaSymbolSolver solver = new JavaSymbolSolver(new ReflectionTypeSolver(false));
        StaticJavaParser.getParserConfiguration().setSymbolResolver(solver);
        final CompilationUnit compilationUnit = StaticJavaParser.parse(code);

        final List<String> returnTypes = compilationUnit.findAll(MethodDeclaration.class).stream()
                .map(md -> md.resolve())
                .map(rmd -> rmd.getReturnType().describe())
                .collect(Collectors.toList());

        returnTypes.forEach(type -> assertEquals("Activity.Timestamps", type));
    }

    /**
     * A type parameter shadows a same-named type declared in an enclosing scope (JLS 6.4.1), so
     * {@code Holder<T>}'s own {@code T} must win over the top-level class {@code T}.
     */
    @Test
    void typeParameterShadowsSameNamedTopLevelClass() {
        String code = "class T {}\n"
                + "class Holder<T> {\n"
                + "    T get() { return null; }\n"
                + "}\n"
                + "class Usage {\n"
                + "    void m(Holder<String> holder) {\n"
                + "        holder.get();\n"
                + "    }\n"
                + "}";

        JavaParserAdapter parser = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()));
        CompilationUnit cu = parser.parse(code);

        MethodCallExpr mce = cu.findAll(MethodCallExpr.class).get(0);

        assertEquals("java.lang.String", mce.calculateResolvedType().describe());
    }

    /**
     * A nested class' type parameter shadows the enclosing class' identically named one. Resolving
     * {@code Aggregator}'s {@code T} to {@code Runner}'s used to drop the {@code Void} argument, leaving
     * the receiver as {@code FailFastRunner<Runner.T>}. Its ancestor {@code Runner<List<T>>} then reported
     * the value of {@code Runner}'s {@code T} as {@code List<T>} - a value mentioning the very type
     * parameter being replaced - so substituting it recursed until the stack overflowed.
     */
    @Test
    void nestedTypeParameterShadowsEnclosingOneWithSameName() {
        String code = "import java.util.List;\n"
                + "class Runner<T> {\n"
                + "    Runner<T> onFailure() { return this; }\n"
                + "    static class Aggregator<T> {\n"
                + "        FailFastRunner<T> failFastRunner() { return null; }\n"
                + "    }\n"
                + "}\n"
                + "final class FailFastRunner<T> extends Runner<List<T>> {}\n"
                + "class Usage {\n"
                + "    void m(Runner.Aggregator<Void> aggregator) {\n"
                + "        aggregator.failFastRunner().onFailure();\n"
                + "    }\n"
                + "}";

        JavaParserAdapter parser = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()));
        CompilationUnit cu = parser.parse(code);

        MethodCallExpr onFailure = cu.findAll(MethodCallExpr.class).get(0);

        assertEquals(
                "Runner<java.util.List<java.lang.Void>>",
                onFailure.calculateResolvedType().describe());
    }
}
