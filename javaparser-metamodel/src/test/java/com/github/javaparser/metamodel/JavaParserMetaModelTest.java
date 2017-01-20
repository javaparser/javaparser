package com.github.javaparser.metamodel;

import org.junit.Test;

public class JavaParserMetaModelTest {
    @Test
    public void outputEverythingWithoutFailure() {
        JavaParserMetaModel javaParserMetaModel = new JavaParserMetaModel();
        for (BaseNodeMetaModel classMetaModel : javaParserMetaModel.classMetaModels) {
            for (PropertyMetaModel propertyMetaModel : classMetaModel.propertyMetaModels) {
                System.out.println(classMetaModel.name + "." + propertyMetaModel.name);
            }
        }
        System.out.println(javaParserMetaModel);
    }
}
