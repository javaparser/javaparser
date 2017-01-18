package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodDeclarationMetaModel extends ClassMetaModel {

    MethodDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.MethodDeclaration.class, "MethodDeclaration", "com.github.javaparser.ast.body.MethodDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getIsDefault", "setIsDefault", "isDefault", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getModifiers", "setModifiers", "modifiers", int.class, null, true, false, false, true));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getParameters", "setParameters", "parameters", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getThrownExceptions", "setThrownExceptions", "thrownExceptions", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeParameters", "setTypeParameters", "typeParameters", int.class, null, true, false, true, false));
    }
}

