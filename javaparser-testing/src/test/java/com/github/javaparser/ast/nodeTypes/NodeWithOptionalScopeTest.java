package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.expr.*;
import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class NodeWithOptionalScopeTest {

    @Test
    public void commonExpressionWhichHaveInterfaceNodeWithOptionalScope() {
        NodeWithOptionalScope methodCallExpr = new MethodCallExpr(new NameExpr("A"), "call");
        NodeWithOptionalScope fieldAccessExpr = new FieldAccessExpr(new NameExpr("A"), "field");
        NodeWithOptionalScope methodReferenceExpr = new MethodReferenceExpr();
        NodeWithOptionalScope objectCreationExpr = new ObjectCreationExpr();

        assertTrue(methodCallExpr.getScope().isPresent());
        assertTrue(fieldAccessExpr.getScope().isPresent());
        assertTrue(methodReferenceExpr.getScope().isPresent());
        assertFalse(objectCreationExpr.getScope().isPresent());
    }

}
