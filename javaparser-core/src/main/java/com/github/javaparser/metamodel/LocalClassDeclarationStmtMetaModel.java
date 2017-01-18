package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;

public class LocalClassDeclarationStmtMetaModel extends ClassMetaModel {

    LocalClassDeclarationStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.LocalClassDeclarationStmt.class, "LocalClassDeclarationStmt", "com.github.javaparser.ast.stmt.LocalClassDeclarationStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getClassDeclaration", "setClassDeclaration", "classDeclaration", com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class, getField("classDeclaration"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return LocalClassDeclarationStmt.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

