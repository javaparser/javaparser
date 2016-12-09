package com.github.javaparser.junit.builders;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class NodeWithThrownExceptionsBuildersTest {
    CompilationUnit cu;

    @Before
    public void setup() {
        cu = new CompilationUnit();
    }

    @After
    public void teardown() {
        cu = null;
    }

    @Test
    public void testThrows() {
        MethodDeclaration addMethod = cu.addClass("test").addMethod("foo", Modifier.PUBLIC);
        addMethod.addThrownException(IllegalStateException.class);
        assertEquals(1, addMethod.getThrownExceptions().size());
        assertEquals(true, addMethod.isThrown(IllegalStateException.class));
        addMethod.addThrownException(new ClassOrInterfaceType("Test"));
        assertEquals(2, addMethod.getThrownExceptions().size());
        assertEquals("Test", addMethod.getThrownException(1).toString());
    }
}