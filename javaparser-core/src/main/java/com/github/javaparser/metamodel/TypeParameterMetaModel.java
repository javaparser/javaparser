package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.type.TypeParameter;

public class TypeParameterMetaModel extends ClassMetaModel {

    TypeParameterMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.TypeParameter.class, "TypeParameter", "com.github.javaparser.ast.type.TypeParameter", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField("annotations"), true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField("name"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeBound", "setTypeBound", "typeBound", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField("typeBound"), true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return TypeParameter.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

