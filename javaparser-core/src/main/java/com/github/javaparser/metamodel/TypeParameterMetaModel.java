package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeParameterMetaModel extends ClassMetaModel {

    TypeParameterMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.TypeParameter.class, "TypeParameter", "com.github.javaparser.ast.type.TypeParameter", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnnotations", "setAnnotations", "annotations", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeBound", "setTypeBound", "typeBound", int.class, null, true, false, true, false));
    }
}

