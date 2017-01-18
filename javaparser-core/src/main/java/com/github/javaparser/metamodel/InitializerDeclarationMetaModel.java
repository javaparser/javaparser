package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.body.InitializerDeclaration;

public class InitializerDeclarationMetaModel extends ClassMetaModel {

    InitializerDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.InitializerDeclaration.class, "InitializerDeclaration", "com.github.javaparser.ast.body.InitializerDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField("body"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "isStatic", "setIsStatic", "isStatic", boolean.class, getField("isStatic"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return InitializerDeclaration.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

