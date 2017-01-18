package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class ContinueStmtMetaModel extends ClassMetaModel {

    ContinueStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ContinueStmt.class, "ContinueStmt", "com.github.javaparser.ast.stmt.ContinueStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getLabel", "setLabel", "label", com.github.javaparser.ast.expr.SimpleName.class, null, true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ContinueStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

