package com.github.javaparser.metamodel;

import com.github.javaparser.ast.expr.StringLiteralExpr;
import org.junit.Test;

import java.util.Optional;

import static org.junit.Assert.assertEquals;

class TestMetaModel extends BaseNodeMetaModel {

    public TestMetaModel() {
        super(Optional.empty(), StringLiteralExpr.class, "stri", "com.japa", true, true);
    }
}

public class BaseNodeMetaModelTest {
    @Test
    public void testGetters() {
        TestMetaModel test = new TestMetaModel();

        assertEquals("testMetaModel", test.getMetaModelFieldName());
    }

}
