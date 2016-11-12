package com.github.javaparser.ast;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.observing.AstObserver;
import com.github.javaparser.ast.observing.AstObserverAdapter;
import com.github.javaparser.ast.observing.ObservableProperty;
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

        cu.getClassByName("MyCoolClass").getFieldByName("f").setElementType(new PrimitiveType(PrimitiveType.Primitive.Boolean));
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.element_type changed from int to boolean"), changes);

        cu.getClassByName("MyCoolClass").getMethodsByName("foo").get(0).getParamByName("p").setName("myParam");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.element_type changed from int to boolean",
                "VariableDeclaratorId.name changed from p to myParam"), changes);
    }
}
