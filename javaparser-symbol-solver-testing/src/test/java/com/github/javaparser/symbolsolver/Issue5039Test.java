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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

/**
 * Reproducer for <a href="https://github.com/javaparser/javaparser/issues/5039">#5039</a>.
 *
 * <p>{@code B<P> extends A<P>} inherits {@code A.fn} without redeclaring it. Resolving
 * {@code op.fn(x)} when {@code op} is {@code B<R>} used to throw {@code MethodAmbiguityException}
 * because reflection collected the same method twice: once via {@code Class.getMethods()}
 * (unsubstituted {@code T}) and once via the ancestor walk (substituted {@code R}).
 */
public class Issue5039Test extends AbstractResolutionTest {

    public interface A<T> {
        T fn(T val);
    }

    public interface B<P> extends A<P> {}

    public interface DefaultA<T> {
        default T fn(T val) {
            return val;
        }
    }

    public interface DefaultB<P> extends DefaultA<P> {}

    public abstract static class Impl<P> implements B<P> {}

    private static MethodCallExpr parseCall(String code) {
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);
        return StaticJavaParser.parse(code).findFirst(MethodCallExpr.class).get();
    }

    private static void assertResolvedToTypeVariableR(MethodCallExpr call) {
        assertEquals("R", call.calculateResolvedType().describe());
        assertEquals("LX.R;", call.calculateResolvedType().toDescriptor());
    }

    @Test
    void inheritedMethodOnCompiledGenericInterfaceIsNotAmbiguous() {
        assertResolvedToTypeVariableR(
                parseCall("class X<R> { R b(R x, " + B.class.getCanonicalName() + "<R> op) { return op.fn(x); } }"));
    }

    @Test
    void inheritedMethodOnSourceGenericInterfaceIsNotAmbiguous() {
        assertResolvedToTypeVariableR(parseCall("interface A<T> { T fn(T val); }\n"
                + "interface B<P> extends A<P> {}\n"
                + "class X<R> { R b(R x, B<R> op) { return op.fn(x); } }"));
    }

    @Test
    void inheritedDefaultMethodOnCompiledGenericInterfaceIsNotAmbiguous() {
        assertResolvedToTypeVariableR(parseCall(
                "class X<R> { R b(R x, " + DefaultB.class.getCanonicalName() + "<R> op) { return op.fn(x); } }"));
    }

    @Test
    void inheritedMethodOnCompiledClassImplementingGenericInterfaceIsNotAmbiguous() {
        assertResolvedToTypeVariableR(
                parseCall("class X<R> { R b(R x, " + Impl.class.getCanonicalName() + "<R> op) { return op.fn(x); } }"));
    }
}
