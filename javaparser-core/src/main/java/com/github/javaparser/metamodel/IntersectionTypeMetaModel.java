package com.github.javaparser.metamodel;

import java.util.Optional;

public class IntersectionTypeMetaModel extends ClassMetaModel {

    IntersectionTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.IntersectionType.class, "IntersectionType", "com.github.javaparser.ast.type.IntersectionType", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getElements", "setElements", "elements", int.class, null, true, false, true, false));
    }
}

