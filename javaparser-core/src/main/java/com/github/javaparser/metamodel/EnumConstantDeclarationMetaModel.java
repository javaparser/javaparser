package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class EnumConstantDeclarationMetaModel extends ClassMetaModel {

    EnumConstantDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.EnumConstantDeclaration.class, "EnumConstantDeclaration", "com.github.javaparser.ast.body.EnumConstantDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getArguments", "setArguments", "arguments", com.github.javaparser.ast.expr.Expression.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getClassBody", "setClassBody", "classBody", com.github.javaparser.ast.body.BodyDeclaration.class, null, true, false, true, false, true));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return EnumConstantDeclarationMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

