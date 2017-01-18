package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.ArrayCreationLevel;

public class ArrayCreationLevelMetaModel extends ClassMetaModel {

    ArrayCreationLevelMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.ArrayCreationLevel.class, "ArrayCreationLevel", "com.github.javaparser.ast.ArrayCreationLevel", "com.github.javaparser.ast", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField("annotations"), true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getDimension", "setDimension", "dimension", com.github.javaparser.ast.expr.Expression.class, getField("dimension"), true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ArrayCreationLevel.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

