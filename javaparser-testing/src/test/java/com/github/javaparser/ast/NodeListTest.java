package com.github.javaparser.ast;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.observing.AstObserver;
import com.github.javaparser.ast.observing.AstObserverAdapter;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.Test;

import java.util.*;

import static org.junit.Assert.assertEquals;

public class NodeListTest {

    private AstObserver createObserver(List<String> changes) {
        return new AstObserver() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("change of property %s for %s: from '%s' to '%s'", property, observedNode, oldValue, newValue ));
            }

            @Override
            public void parentChange(Node observedNode, Node previousParent, Node newParent) {
                changes.add(String.format("setting parent for %s: was %s, now is %s", observedNode, previousParent, newParent));
            }

            @Override
            public void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                changes.add(String.format("'%s' %s in list at %d", nodeAddedOrRemoved, type, index));
            }
        };
    }

    private FieldDeclaration createIntField(String name) {
        return new FieldDeclaration(EnumSet.noneOf(Modifier.class), PrimitiveType.INT_TYPE, name);
    }

    @Test
    public void addAllWithoutIndex() {
        List<String> changes = new LinkedList<>();
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A");
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().addAll(Arrays.asList(createIntField("a"), createIntField("b"), createIntField("c")));
        assertEquals(Arrays.asList("'int a;' ADDITION in list at 1",
                "'int b;' ADDITION in list at 2",
                "'int c;' ADDITION in list at 3"), changes);
    }

    @Test
    public void addAllWithIndex() {
        List<String> changes = new LinkedList<>();
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A");
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().addAll(0, Arrays.asList(createIntField("a"), createIntField("b"), createIntField("c")));
        assertEquals(Arrays.asList("'int a;' ADDITION in list at 0",
                "'int b;' ADDITION in list at 1",
                "'int c;' ADDITION in list at 2"), changes);
    }

    @Test
    public void clear() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A");
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().clear();
        assertEquals(Arrays.asList("'int a;' REMOVAL in list at 0",
                "'int b;' REMOVAL in list at 0",
                "'int c;' REMOVAL in list at 0"), changes);
    }

    @Test
    public void set() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A");
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().set(1, createIntField("d"));
        assertEquals(Arrays.asList("'int b;' REMOVAL in list at 1",
                "'int d;' ADDITION in list at 1"), changes);
    }

    @Test
    public void removeNode() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; int d; int e; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A");
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().remove(cd.getFieldByName("c"));
        assertEquals(Arrays.asList("'int c;' REMOVAL in list at 2"), changes);
    }

    @Test
    public void removeObject() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; int d; int e; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A");
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().remove("hi");
        assertEquals(Arrays.asList(), changes);
    }

    @Test
    public void removeAll() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; int d; int e; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A");
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().removeAll(Arrays.asList(cd.getFieldByName("b"), "foo", cd.getFieldByName("d")));
        assertEquals(Arrays.asList("'int b;' REMOVAL in list at 1",
                "'int d;' REMOVAL in list at 2"), changes);
    }
}
