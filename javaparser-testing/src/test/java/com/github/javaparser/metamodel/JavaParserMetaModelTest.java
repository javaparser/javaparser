package com.github.javaparser.metamodel;

import org.junit.Test;

public class JavaParserMetaModelTest {
    @Test
    public void outputEverythingWithoutFailure() {
        JavaParserMetaModel javaParserMetaModel = new JavaParserMetaModel();
        for (ClassMetaModel classMetaModel : javaParserMetaModel.getClassMetaModels()) {
            for (FieldMetaModel fieldMetaModel : classMetaModel.fieldMetaModels) {
                System.out.println(classMetaModel.name + "." + fieldMetaModel.name);
            }
        }
        System.out.println(javaParserMetaModel);
    }
}
