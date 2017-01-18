package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.type.WildcardType;

public class WildcardTypeMetaModel extends ClassMetaModel {

    WildcardTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.WildcardType.class, "WildcardType", "com.github.javaparser.ast.type.WildcardType", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExtendedTypes", "setExtendedTypes", "extendedTypes", com.github.javaparser.ast.type.ReferenceType.class, getField("extendedTypes"), true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getSuperTypes", "setSuperTypes", "superTypes", com.github.javaparser.ast.type.ReferenceType.class, getField("superTypes"), true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return WildcardType.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

