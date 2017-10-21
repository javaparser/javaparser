package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.expr.*;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class NodeWithOptionalScopeTest {

    @Test
    public void commonExpressionWhichHaveInterfaceNodeWithOptionalScope() {
        NodeWithOptionalScope methodCallExpr = new MethodCallExpr(new NameExpr("A"), "call");
        NodeWithOptionalScope objectCreationExpr = new ObjectCreationExpr();

        assertEquals(true, methodCallExpr.getScope().isPresent());
        assertEquals(false, objectCreationExpr.getScope().isPresent());
    }

    @Test
    public void removeScope() {
        MethodCallExpr methodCallExpr = new MethodCallExpr(new NameExpr("A"), "method");

        methodCallExpr.removeScope();

        assertEquals(false, methodCallExpr.getScope().isPresent());
    }
}
