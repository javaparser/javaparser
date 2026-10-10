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
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Overloads that only differ by type variables of their declaring type, such as {@code setId(T, String)}
 * and {@code setId(U, String)} in {@code GenericClass<T, U>}, used to be compared on their declared
 * signatures even when inherited through {@code extends GenericClass<ConcreteClass, ConcreteCcClass>} or
 * called on a {@code GenericClass<ConcreteClass, ConcreteCcClass>}. Both then looked applicable and neither
 * more specific, and every call failed with a {@code MethodAmbiguityException}. They must be compared on
 * {@code setId(ConcreteClass, String)} and {@code setId(ConcreteCcClass, String)}, as javac does.
 * <p>
 * Not covered, and therefore not tested here, with the overload javac selects:
 * <ul>
 *   <li>a raw receiver or a raw ancestor ({@code class RawSub extends GenericClass}): javac compares the erased
 *   signatures and selects {@code setId(T, String)} for a {@code ConcreteClass} argument, whereas the call stays
 *   ambiguous;</li>
 *   <li>{@code null} passed on a wildcard receiver ({@code GenericClass<? extends ConcreteClass, ConcreteCcClass>}):
 *   javac selects {@code setId(T, String)}, whereas {@code setId(U, String)} is selected;</li>
 *   <li>a method reference such as {@code generic::setId}: javac selects the overload that suits the target
 *   functional interface, whereas the reference stays ambiguous;</li>
 *   <li>a receiver whose type comes from Reflection or Javassist, which is still resolved on its declared
 *   signatures.</li>
 * </ul>
 */
class Issue4628Test extends AbstractResolutionTest {

    private static final String CODE = "class ConcreteCcClass extends ConcreteClass {}\n"
            + "class ConcreteClass extends GenericClass<ConcreteClass, ConcreteCcClass> {\n"
            + "    void calls(ConcreteClass receiver, Sub sub) {\n"
            + "        this.setId(new ConcreteClass(), \"this, only T applicable\");\n"
            + "        this.setId(new ConcreteCcClass(), \"this, U more specific\");\n"
            + "        setId(new ConcreteClass(), \"unqualified, only T applicable\");\n"
            + "        setId(new ConcreteCcClass(), \"unqualified, U more specific\");\n"
            + "        receiver.setId(new ConcreteClass(), \"variable, only T applicable\");\n"
            + "        receiver.setId(new ConcreteCcClass(), \"variable, U more specific\");\n"
            + "        sub.setId(new ConcreteClass(), \"indirect, only T applicable\");\n"
            + "        sub.setId(new ConcreteCcClass(), \"indirect, U more specific\");\n"
            + "        sub.put(\"key\", \"mixed, only K applicable\");\n"
            + "        sub.put(1, \"mixed, only Integer applicable\");\n"
            + "    }\n"
            + "}\n"
            + "class Receivers extends GenericClass<ConcreteClass, ConcreteCcClass> {\n"
            + "    <X extends GenericClass<ConcreteClass, ConcreteCcClass>> void calls(\n"
            + "            GenericClass<ConcreteClass, ConcreteCcClass> generic, X bounded,\n"
            + "            GenericClass<? extends ConcreteClass, ConcreteCcClass> wildcard) {\n"
            + "        generic.setId(new ConcreteClass(), \"parameterized, only T applicable\");\n"
            + "        generic.setId(new ConcreteCcClass(), \"parameterized, U more specific\");\n"
            + "        super.setId(new ConcreteClass(), \"super, only T applicable\");\n"
            + "        super.setId(new ConcreteCcClass(), \"super, U more specific\");\n"
            + "        bounded.setId(new ConcreteClass(), \"type variable, only T applicable\");\n"
            + "        bounded.setId(new ConcreteCcClass(), \"type variable, U more specific\");\n"
            + "        wildcard.setId(new ConcreteCcClass(), \"wildcard, only U applicable\");\n"
            + "    }\n"
            + "}\n"
            + "class Sub extends Mid<String> {}\n"
            + "class Mid<K> extends GenericClass<ConcreteClass, ConcreteCcClass> {\n"
            + "    void put(K key, String label) {}\n"
            + "    void put(Integer key, String label) {}\n"
            + "}\n"
            + "class GenericClass<T extends GenericClass, U> {\n"
            + "    GenericClass setId(T t, String idName) { return this; }\n"
            + "    GenericClass setId(U u, String idName) { return this; }\n"
            + "}\n";

    private CompilationUnit cu;

    @BeforeEach
    void parse() {
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        StaticJavaParser.setConfiguration(config);
        cu = StaticJavaParser.parse(CODE);
    }

    /**
     * The call whose second argument is the string literal {@code label}: each call of {@link #CODE} is labelled
     * with the case it covers, as javac sees it: which overloads are applicable, or which one is more specific.
     */
    private MethodCallExpr call(String label) {
        return cu.findFirst(MethodCallExpr.class, c -> c.getArguments()
                        .get(1)
                        .asStringLiteralExpr()
                        .getValue()
                        .equals(label))
                .get();
    }

    /**
     * The qualified signature of the method the labelled call resolves to. It names the overload by its declared
     * parameter types, {@code T} or {@code U}, whatever the type arguments the call is resolved with.
     */
    private String resolve(String label) {
        return call(label).resolve().getQualifiedSignature();
    }

    @Test
    void inheritedOverloadsAreComparedWithTheTypeArgumentsOfTheAncestor() {
        assertEquals("GenericClass.setId(T, java.lang.String)", resolve("this, only T applicable"));
        assertEquals("GenericClass.setId(U, java.lang.String)", resolve("this, U more specific"));
        assertEquals("GenericClass.setId(T, java.lang.String)", resolve("unqualified, only T applicable"));
        assertEquals("GenericClass.setId(U, java.lang.String)", resolve("unqualified, U more specific"));
        assertEquals("GenericClass.setId(T, java.lang.String)", resolve("variable, only T applicable"));
        assertEquals("GenericClass.setId(U, java.lang.String)", resolve("variable, U more specific"));
    }

    @Test
    void typeArgumentsArePropagatedThroughIntermediateAncestors() {
        assertEquals("GenericClass.setId(T, java.lang.String)", resolve("indirect, only T applicable"));
        assertEquals("GenericClass.setId(U, java.lang.String)", resolve("indirect, U more specific"));
    }

    @Test
    void overloadsMixingTypeVariablesAndConcreteTypesAreStillResolved() {
        assertEquals("Mid.put(K, java.lang.String)", resolve("mixed, only K applicable"));
        assertEquals("Mid.put(java.lang.Integer, java.lang.String)", resolve("mixed, only Integer applicable"));
    }

    @Test
    void overloadsCalledOnAParameterizedReceiverAreComparedWithItsTypeArguments() {
        assertEquals("GenericClass.setId(T, java.lang.String)", resolve("parameterized, only T applicable"));
        assertEquals("GenericClass.setId(U, java.lang.String)", resolve("parameterized, U more specific"));
        assertEquals("GenericClass.setId(T, java.lang.String)", resolve("super, only T applicable"));
        assertEquals("GenericClass.setId(U, java.lang.String)", resolve("super, U more specific"));
        assertEquals("GenericClass.setId(T, java.lang.String)", resolve("type variable, only T applicable"));
        assertEquals("GenericClass.setId(U, java.lang.String)", resolve("type variable, U more specific"));
        assertEquals(
                "GenericClass",
                call("parameterized, U more specific").calculateResolvedType().describe());
    }

    @Test
    void overloadsCalledOnAWildcardParameterizedReceiverAreStillResolved() {
        assertEquals("GenericClass.setId(U, java.lang.String)", resolve("wildcard, only U applicable"));
    }
}
