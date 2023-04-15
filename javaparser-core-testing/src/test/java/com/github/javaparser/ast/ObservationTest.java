/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.ast;

import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.AstObserverAdapter;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ObservationTest {

    @Test
    void registerSubTree() {
        String code = "class A { int f; void foo(int p) { return 'z'; }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.registerForSubtree(observer);

        assertThat(changes).isEmpty();

        cu.getClassByName("A").get().setName("MyCoolClass");
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass");

        cu.getClassByName("MyCoolClass").get().getFieldByName("f").get().getVariable(0).setType(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN));
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean");

        cu.getClassByName("MyCoolClass").get().getMethodsByName("foo").get(0).getParameterByName("p").get().setName("myParam");
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam");
    }

    @Test
    void registerWithJustNodeMode() {
        String code = "class A { int f; void foo(int p) { return 'z'; }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.getClassByName("A").get().register(observer, Node.ObserverRegistrationMode.JUST_THIS_NODE);

        assertThat(changes).isEmpty();

        cu.getClassByName("A").get().setName("MyCoolClass");
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass");

        cu.getClassByName("MyCoolClass").get().getFieldByName("f").get().getVariable(0).setType(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN));
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass");

        cu.getClassByName("MyCoolClass").get().getMethodsByName("foo").get(0).getParameterByName("p").get().setName("myParam");
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass");

        cu.getClassByName("MyCoolClass").get().addField("int", "bar").getVariables().get(0).setInitializer("0");
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass");
    }

    @Test
    void registerWithNodeAndExistingDescendantsMode() {
        String code = "class A { int f; void foo(int p) { return 'z'; }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.getClassByName("A").get().register(observer, Node.ObserverRegistrationMode.THIS_NODE_AND_EXISTING_DESCENDANTS);

        assertThat(changes).isEmpty();

        cu.getClassByName("A").get().setName("MyCoolClass");
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass");

        cu.getClassByName("MyCoolClass").get().getFieldByName("f").get().getVariable(0).setType(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN));
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean");

        cu.getClassByName("MyCoolClass").get().getMethodsByName("foo").get(0).getParameterByName("p").get().setName("myParam");
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam");

        cu.getClassByName("MyCoolClass").get().addField("int", "bar").getVariables().get(0).setInitializer("0");
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam");
    }

    @Test
    void registerWithSelfPropagatingMode() {
        String code = "class A { int f; void foo(int p) { return 'z'; }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.getClassByName("A").get().register(observer, Node.ObserverRegistrationMode.SELF_PROPAGATING);

        assertThat(changes).isEmpty();

        cu.getClassByName("A").get().setName("MyCoolClass");
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass");

        cu.getClassByName("MyCoolClass").get().getFieldByName("f").get().getVariable(0).setType(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN));
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean");

        cu.getClassByName("MyCoolClass").get().getMethodsByName("foo").get(0).getParameterByName("p").get().setName("myParam");
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam");

        cu.getClassByName("MyCoolClass").get()
                .addField("int", "bar")
                .getVariables().get(0).setInitializer("0");
        assertThat(changes).containsExactlyInAnyOrder("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam",
                "VariableDeclarator.initializer changed from null to 0");
    }

    @Test
    void deleteAParameterTriggerNotifications() {
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {

            @Override
            public void listChange(NodeList<?> observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                changes.add("removing [" + nodeAddedOrRemoved + "] from index " + index);
            }
        };
        cu.register(observer, Node.ObserverRegistrationMode.SELF_PROPAGATING);

        cu.getClassByName("A").get().getMethodsByName("foo").get(0).getParameter(0).remove();
        assertThat(changes).containsExactlyInAnyOrder("removing [int p] from index 0");
    }

    @Test
    void deleteClassNameDoesNotTriggerNotifications() {
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {

            @Override
            public void listChange(NodeList<?> observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                changes.add("removing [" + nodeAddedOrRemoved + "] from index " + index);
            }
        };
        cu.register(observer, Node.ObserverRegistrationMode.SELF_PROPAGATING);

        // I cannot remove the name of a type
        assertFalse(cu.getClassByName("A").get().getName().remove());
        assertThat(changes).isEmpty();
    }

    @Test
    void deleteMethodBodyDoesTriggerNotifications() {
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {

            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add("setting [" + property + "] to " + newValue);
            }

            @Override
            public void listChange(NodeList<?> observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                changes.add("removing [" + nodeAddedOrRemoved + "] from index " + index);
            }
        };
        cu.register(observer, Node.ObserverRegistrationMode.SELF_PROPAGATING);

        assertTrue(cu.getClassByName("A").get().getMethodsByName("foo").get(0).getBody().get().remove());
        assertThat(changes).containsExactlyInAnyOrder("setting [BODY] to null");
    }

}
