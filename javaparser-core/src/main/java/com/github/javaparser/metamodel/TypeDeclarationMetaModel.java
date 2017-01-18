package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class TypeDeclarationMetaModel extends ClassMetaModel {

    TypeDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.TypeDeclaration.class, "TypeDeclaration", "com.github.javaparser.ast.body.TypeDeclaration", "com.github.javaparser.ast.body", true);
        fieldMetaModels.add(new FieldMetaModel(this, "getMembers", "setMembers", "members", com.github.javaparser.ast.body.BodyDeclaration.class, null, true, false, true, false, true));
        fieldMetaModels.add(new FieldMetaModel(this, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, null, true, false, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return TypeDeclarationMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

