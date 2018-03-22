package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.expr.*;
import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class NodeWithOptionalScopeTest {

    @Test
    public void commonExpressionWhichHaveInterfaceNodeWithOptionalScope() {
        NodeWithOptionalScope methodCallExpr = new MethodCallExpr(new NameExpr("A"), "call");
        NodeWithOptionalScope objectCreationExpr = new ObjectCreationExpr();

        assertTrue(methodCallExpr.getScope().isPresent());
        assertFalse(objectCreationExpr.getScope().isPresent());
    }

    @Test
    public void removeScope() {
        MethodCallExpr methodCallExpr = new MethodCallExpr(new NameExpr("A"), "method");

        methodCallExpr.removeScope();

        assertFalse(methodCallExpr.getScope().isPresent());
    }
}
