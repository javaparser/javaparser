package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class InitializerDeclarationMetaModel extends ClassMetaModel {

    InitializerDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.InitializerDeclaration.class, "InitializerDeclaration", "com.github.javaparser.ast.body.InitializerDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "isStatic", "setIsStatic", "isStatic", boolean.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return InitializerDeclarationMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

