package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class BreakStmtMetaModel extends ClassMetaModel {

    BreakStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.BreakStmt.class, "BreakStmt", "com.github.javaparser.ast.stmt.BreakStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getLabel", "setLabel", "label", com.github.javaparser.ast.expr.SimpleName.class, null, true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return BreakStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

