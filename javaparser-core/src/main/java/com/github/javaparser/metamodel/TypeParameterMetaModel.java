package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class TypeParameterMetaModel extends ClassMetaModel {

    TypeParameterMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.TypeParameter.class, "TypeParameter", "com.github.javaparser.ast.type.TypeParameter", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeBound", "setTypeBound", "typeBound", com.github.javaparser.ast.type.ClassOrInterfaceType.class, null, true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return TypeParameterMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

