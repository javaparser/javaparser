package com.github.javaparser.metamodel;

import org.junit.Test;

public class JavaParserMetaModelTest {
    @Test
    public void outputEverythingWithoutFailure() {
        for (BaseNodeMetaModel classMetaModel : JavaParserMetaModel.getNodeMetaModels()) {
            for (PropertyMetaModel propertyMetaModel : classMetaModel.getDeclaredPropertyMetaModels()) {
                System.out.println(classMetaModel.getTypeNameGenerified() + "." + propertyMetaModel.getName());
            }
        }
    }
}
