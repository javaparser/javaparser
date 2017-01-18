package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class ConstructorDeclarationMetaModel extends ClassMetaModel {

    ConstructorDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.ConstructorDeclaration.class, "ConstructorDeclaration", "com.github.javaparser.ast.body.ConstructorDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, null, true, false, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getParameters", "setParameters", "parameters", com.github.javaparser.ast.body.Parameter.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getThrownExceptions", "setThrownExceptions", "thrownExceptions", com.github.javaparser.ast.type.ReferenceType.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeParameters", "setTypeParameters", "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, null, true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return ConstructorDeclarationMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

