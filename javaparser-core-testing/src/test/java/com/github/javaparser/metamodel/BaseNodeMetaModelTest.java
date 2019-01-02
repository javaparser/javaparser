package com.github.javaparser.metamodel;

import com.github.javaparser.ast.expr.StringLiteralExpr;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

class TestMetaModel extends BaseNodeMetaModel {

    public TestMetaModel() {
        super(Optional.empty(), StringLiteralExpr.class, "stri", "com.japa", true, true);
    }
}

class BaseNodeMetaModelTest {
    @Test
    void testGetters() {
        TestMetaModel test = new TestMetaModel();

        assertEquals("testMetaModel", test.getMetaModelFieldName());
    }

}
