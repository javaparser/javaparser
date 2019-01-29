package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.expr.*;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class NodeWithOptionalScopeTest {

    @Test
    void commonExpressionWhichHaveInterfaceNodeWithOptionalScope() {
        NodeWithOptionalScope methodCallExpr = new MethodCallExpr(new NameExpr("A"), "call");
        NodeWithOptionalScope objectCreationExpr = new ObjectCreationExpr();

        assertTrue(methodCallExpr.getScope().isPresent());
        assertFalse(objectCreationExpr.getScope().isPresent());
    }

    @Test
    void removeScope() {
        MethodCallExpr methodCallExpr = new MethodCallExpr(new NameExpr("A"), "method");

        methodCallExpr.removeScope();

        assertFalse(methodCallExpr.getScope().isPresent());
    }
}
