package com.github.javaparser.metamodel;

import com.github.javaparser.ast.Node;
import org.junit.Test;

import java.lang.reflect.Field;

public class JavaParserMetaModelTest {
    @Test
    public void outputEverythingWithoutFailure() {
        JavaParserMetaModel javaParserMetaModel = new JavaParserMetaModel();
        for (ClassMetaModel classMetaModel : javaParserMetaModel.getClassMetaModels()) {
            for (FieldMetaModel fieldMetaModel : classMetaModel.fieldMetaModels) {
                System.out.println(classMetaModel.name + "." + fieldMetaModel.name);
            }
        }
    }
}
