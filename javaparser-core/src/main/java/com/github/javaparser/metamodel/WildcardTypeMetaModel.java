package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class WildcardTypeMetaModel extends ClassMetaModel {

    WildcardTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.WildcardType.class, "WildcardType", "com.github.javaparser.ast.type.WildcardType", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExtendedTypes", "setExtendedTypes", "extendedTypes", com.github.javaparser.ast.type.ReferenceType.class, null, true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getSuperTypes", "setSuperTypes", "superTypes", com.github.javaparser.ast.type.ReferenceType.class, null, true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return WildcardTypeMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

