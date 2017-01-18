package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayCreationLevelMetaModel extends ClassMetaModel {

    ArrayCreationLevelMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.ArrayCreationLevel.class, "ArrayCreationLevel", "com.github.javaparser.ast.ArrayCreationLevel", "com.github.javaparser.ast", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnnotations", "setAnnotations", "annotations", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getDimension", "setDimension", "dimension", int.class, null, true, false, false, false));
    }
}

