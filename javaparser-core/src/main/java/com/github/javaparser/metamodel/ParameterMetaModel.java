package com.github.javaparser.metamodel;

import java.util.Optional;

public class ParameterMetaModel extends ClassMetaModel {

    ParameterMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.Parameter.class, "Parameter", "com.github.javaparser.ast.body.Parameter", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnnotations", "setAnnotations", "annotations", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "isVarArgs", "setIsVarArgs", "isVarArgs", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getModifiers", "setModifiers", "modifiers", int.class, null, true, false, false, true));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", int.class, null, true, false, false, false));
    }
}

