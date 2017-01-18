package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.type.UnionType;

public class UnionTypeMetaModel extends ClassMetaModel {

    UnionTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.UnionType.class, "UnionType", "com.github.javaparser.ast.type.UnionType", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getElements", "setElements", "elements", com.github.javaparser.ast.type.ReferenceType.class, getField("elements"), true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return UnionType.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

