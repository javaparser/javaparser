package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayTypeMetaModel extends ClassMetaModel {

    ArrayTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.ArrayType.class, "ArrayType", "com.github.javaparser.ast.type.ArrayType", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getComponentType", "setComponentType", "componentType", int.class, null, true, false, false, false));
    }
}

