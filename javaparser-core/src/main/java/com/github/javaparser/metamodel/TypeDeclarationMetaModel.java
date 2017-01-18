package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeDeclarationMetaModel extends ClassMetaModel {

    TypeDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.TypeDeclaration.class, "TypeDeclaration", "com.github.javaparser.ast.body.TypeDeclaration", "com.github.javaparser.ast.body", true);
        fieldMetaModels.add(new FieldMetaModel(this, "getMembers", "setMembers", "members", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getModifiers", "setModifiers", "modifiers", int.class, null, true, false, false, true));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", int.class, null, true, false, false, false));
    }
}

