package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.body.MethodDeclaration;

public class MethodDeclarationMetaModel extends ClassMetaModel {

    MethodDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.MethodDeclaration.class, "MethodDeclaration", "com.github.javaparser.ast.body.MethodDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField("body"), true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "isDefault", "setIsDefault", "isDefault", boolean.class, getField("isDefault"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField("modifiers"), true, false, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField("name"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getParameters", "setParameters", "parameters", com.github.javaparser.ast.body.Parameter.class, getField("parameters"), true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getThrownExceptions", "setThrownExceptions", "thrownExceptions", com.github.javaparser.ast.type.ReferenceType.class, getField("thrownExceptions"), true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField("type"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeParameters", "setTypeParameters", "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, getField("typeParameters"), true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return MethodDeclaration.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

