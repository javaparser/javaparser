package com.github.javaparser.metamodel;

import java.util.Optional;

public class WildcardTypeMetaModel extends ClassMetaModel {

    WildcardTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.WildcardType.class, "WildcardType", "com.github.javaparser.ast.type.WildcardType", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExtendedTypes", "setExtendedTypes", "extendedTypes", int.class, null, true, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getSuperTypes", "setSuperTypes", "superTypes", int.class, null, true, true, false, false));
    }
}

