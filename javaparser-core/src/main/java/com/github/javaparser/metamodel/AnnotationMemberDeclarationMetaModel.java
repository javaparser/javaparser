package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationMemberDeclarationMetaModel extends ClassMetaModel {

    AnnotationMemberDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.AnnotationMemberDeclaration.class, "AnnotationMemberDeclaration", "com.github.javaparser.ast.body.AnnotationMemberDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getDefaultValue", "setDefaultValue", "defaultValue", int.class, null, true, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getModifiers", "setModifiers", "modifiers", int.class, null, true, false, false, true));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", int.class, null, true, false, false, false));
    }
}

