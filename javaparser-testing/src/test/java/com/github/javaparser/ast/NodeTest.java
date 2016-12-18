/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.AstObserverAdapter;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class NodeTest {

    @Test
    public void registerSubTree() {
        String code = "class A { int f; void foo(int p) { return 'z'; }}";
        CompilationUnit cu = JavaParser.parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.registerForSubtree(observer);

        assertEquals(Arrays.asList(), changes);

        cu.getClassByName("A").setName("MyCoolClass");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);

        cu.getClassByName("MyCoolClass").getFieldByName("f").getVariable(0).setType(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN));
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "VariableDeclarator.type changed from int to boolean"), changes);

        cu.getClassByName("MyCoolClass").getMethodsByName("foo").get(0).getParamByName("p").setName("myParam");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam"), changes);
    }

    @Test
    public void registerWithJustNodeMode() {
        String code = "class A { int f; void foo(int p) { return 'z'; }}";
        CompilationUnit cu = JavaParser.parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.getClassByName("A").register(observer, Node.ObserverRegistrationMode.JUST_THIS_NODE);

        assertEquals(Arrays.asList(), changes);

        cu.getClassByName("A").setName("MyCoolClass");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);

        cu.getClassByName("MyCoolClass").getFieldByName("f").getVariable(0).setType(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN));
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);

        cu.getClassByName("MyCoolClass").getMethodsByName("foo").get(0).getParamByName("p").setName("myParam");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);

        cu.getClassByName("MyCoolClass").addField("int", "bar").getVariables().get(0).setInitializer("0");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);
    }

    @Test
    public void registerWithNodeAndExistingDescendantsMode() {
        String code = "class A { int f; void foo(int p) { return 'z'; }}";
        CompilationUnit cu = JavaParser.parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.getClassByName("A").register(observer, Node.ObserverRegistrationMode.THIS_NODE_AND_EXISTING_DESCENDANTS);

        assertEquals(Arrays.asList(), changes);

        cu.getClassByName("A").setName("MyCoolClass");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);

        cu.getClassByName("MyCoolClass").getFieldByName("f").getVariable(0).setType(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN));
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "VariableDeclarator.type changed from int to boolean"), changes);

        cu.getClassByName("MyCoolClass").getMethodsByName("foo").get(0).getParamByName("p").setName("myParam");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam"), changes);

        cu.getClassByName("MyCoolClass").addField("int", "bar").getVariables().get(0).setInitializer("0");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam"), changes);
    }

    @Test
    public void registerWithSelfPropagatingMode() {
        String code = "class A { int f; void foo(int p) { return 'z'; }}";
        CompilationUnit cu = JavaParser.parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.getClassByName("A").register(observer, Node.ObserverRegistrationMode.SELF_PROPAGATING);

        assertEquals(Arrays.asList(), changes);

        cu.getClassByName("A").setName("MyCoolClass");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);

        cu.getClassByName("MyCoolClass").getFieldByName("f").getVariable(0).setType(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN));
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "VariableDeclarator.type changed from int to boolean"), changes);

        cu.getClassByName("MyCoolClass").getMethodsByName("foo").get(0).getParamByName("p").setName("myParam");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam"), changes);

        cu.getClassByName("MyCoolClass")
                .addField("int", "bar")
                .getVariables().get(0).setInitializer("0");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam",
                "VariableDeclarator.initializer changed from null to 0"), changes);
    }

    @Test
    public void deleteAParameterTriggerNotifications() {
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = JavaParser.parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {

            @Override
            public void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                changes.add("removing [" + nodeAddedOrRemoved + "] from index " + index);
            }
        };
        cu.register(observer, Node.ObserverRegistrationMode.SELF_PROPAGATING);

        cu.getClassByName("A").getMethodsByName("foo").get(0).getParameter(0).remove();
        assertEquals(Arrays.asList("removing [int p] from index 0"), changes);
    }

    @Test
    public void deleteClassNameDoesNotTriggerNotifications() {
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = JavaParser.parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {

            @Override
            public void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                changes.add("removing [" + nodeAddedOrRemoved + "] from index " + index);
            }
        };
        cu.register(observer, Node.ObserverRegistrationMode.SELF_PROPAGATING);

        // I cannot remove the name of a type
        assertEquals(false, cu.getClassByName("A").getName().remove());
        assertEquals(Arrays.asList(), changes);
    }

    @Test
    public void deleteMethodBodyDoesTriggerNotifications() {
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = JavaParser.parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {

            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add("setting [" + property + "] to " + newValue);
            }

            @Override
            public void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                changes.add("removing [" + nodeAddedOrRemoved + "] from index " + index);
            }
        };
        cu.register(observer, Node.ObserverRegistrationMode.SELF_PROPAGATING);

        assertEquals(true, cu.getClassByName("A").getMethodsByName("foo").get(0).getBody().get().remove());
        assertEquals(Arrays.asList("setting [BODY] to null"), changes);
    }
}
