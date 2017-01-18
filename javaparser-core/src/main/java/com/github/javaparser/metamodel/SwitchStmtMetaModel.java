package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.stmt.SwitchStmt;

public class SwitchStmtMetaModel extends ClassMetaModel {

    SwitchStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.SwitchStmt.class, "SwitchStmt", "com.github.javaparser.ast.stmt.SwitchStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getEntries", "setEntries", "entries", com.github.javaparser.ast.stmt.SwitchEntryStmt.class, getField("entries"), true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getSelector", "setSelector", "selector", com.github.javaparser.ast.expr.Expression.class, getField("selector"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return SwitchStmt.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

