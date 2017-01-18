package com.github.javaparser.metamodel;

import java.util.Optional;

public class EnumConstantDeclarationMetaModel extends ClassMetaModel {

    EnumConstantDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.EnumConstantDeclaration.class, "EnumConstantDeclaration", "com.github.javaparser.ast.body.EnumConstantDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getArguments", "setArguments", "arguments", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getClassBody", "setClassBody", "classBody", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", int.class, null, true, false, false, false));
    }
}

