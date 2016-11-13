package com.github.javaparser.ast.observing;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.VariableDeclaratorId;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class PropagatingAstObserverTest {
    @Test
    public void verifyPropagation() {
        String code = "class A {  }";
        CompilationUnit cu = JavaParser.parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new PropagatingAstObserver() {
            @Override
            public void concretePropertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.registerForSubtree(observer);

        assertEquals(Arrays.asList(), changes);

        FieldDeclaration fieldDeclaration = cu.getClassByName("A").addField("String", "foo");
        assertEquals(Arrays.asList("FieldDeclaration.modifiers changed from [] to []",
                "FieldDeclaration.element_type changed from empty to String",
                "VariableDeclaratorId.array_bracket_pairs_after_id changed from com.github.javaparser.ast.NodeList@1 to com.github.javaparser.ast.NodeList@1"), changes);
        assertEquals(true, fieldDeclaration.isRegistered(observer));

        cu.getClassByName("A").getFieldByName("foo").getVariables().get(0).setId(new VariableDeclaratorId("Bar"));
        assertEquals(Arrays.asList("FieldDeclaration.modifiers changed from [] to []",
                "FieldDeclaration.element_type changed from empty to String",
                "VariableDeclaratorId.array_bracket_pairs_after_id changed from com.github.javaparser.ast.NodeList@1 to com.github.javaparser.ast.NodeList@1",
                "VariableDeclarator.id changed from foo to Bar"), changes);
    }
}
