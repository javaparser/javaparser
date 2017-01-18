package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class IntersectionTypeMetaModel extends ClassMetaModel {

    IntersectionTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.IntersectionType.class, "IntersectionType", "com.github.javaparser.ast.type.IntersectionType", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getElements", "setElements", "elements", com.github.javaparser.ast.type.ReferenceType.class, null, true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return IntersectionTypeMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

