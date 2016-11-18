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
                changes.add(String.format("'%s' %s in list '%s' at %d", nodeAddedOrRemoved, type, nodeAddedOrRemoved, index));
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
        assertEquals(Arrays.asList("'int a;' ADDITION in list 'int a;' at 1",
                "'int b;' ADDITION in list 'int b;' at 2",
                "'int c;' ADDITION in list 'int c;' at 3"), changes);
    }
}
