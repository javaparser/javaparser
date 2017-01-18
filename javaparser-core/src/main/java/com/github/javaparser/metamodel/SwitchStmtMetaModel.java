package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class SwitchStmtMetaModel extends ClassMetaModel {

    SwitchStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.SwitchStmt.class, "SwitchStmt", "com.github.javaparser.ast.stmt.SwitchStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getEntries", "setEntries", "entries", com.github.javaparser.ast.stmt.SwitchEntryStmt.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getSelector", "setSelector", "selector", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return SwitchStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

