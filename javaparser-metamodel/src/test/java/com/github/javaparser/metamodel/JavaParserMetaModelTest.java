package com.github.javaparser.metamodel;

import org.junit.Test;

public class JavaParserMetaModelTest {
    @Test
    public void outputEverythingWithoutFailure() {
        JavaParserMetaModel javaParserMetaModel = new JavaParserMetaModel();
        for (BaseNodeMetaModel classMetaModel : javaParserMetaModel.getNodeMetaModels()) {
            for (PropertyMetaModel propertyMetaModel : classMetaModel.getDeclaredPropertyMetaModels()) {
                System.out.println(classMetaModel.getTypeNameGenerified() + "." + propertyMetaModel.getName());
            }
        }
        System.out.println(javaParserMetaModel);
    }
}
