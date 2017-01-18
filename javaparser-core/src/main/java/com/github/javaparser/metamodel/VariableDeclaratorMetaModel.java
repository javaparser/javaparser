package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.body.VariableDeclarator;

public class VariableDeclaratorMetaModel extends ClassMetaModel {

    VariableDeclaratorMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.VariableDeclarator.class, "VariableDeclarator", "com.github.javaparser.ast.body.VariableDeclarator", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getInitializer", "setInitializer", "initializer", com.github.javaparser.ast.expr.Expression.class, getField("initializer"), true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField("name"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField("type"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return VariableDeclarator.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

