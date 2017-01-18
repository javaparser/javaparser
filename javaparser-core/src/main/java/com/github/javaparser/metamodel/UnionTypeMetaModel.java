package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnionTypeMetaModel extends ClassMetaModel {

    UnionTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.UnionType.class, "UnionType", "com.github.javaparser.ast.type.UnionType", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getElements", "setElements", "elements", int.class, null, true, false, true, false));
    }
}

