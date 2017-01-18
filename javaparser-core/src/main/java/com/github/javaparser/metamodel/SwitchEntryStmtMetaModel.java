package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class SwitchEntryStmtMetaModel extends ClassMetaModel {

    SwitchEntryStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.SwitchEntryStmt.class, "SwitchEntryStmt", "com.github.javaparser.ast.stmt.SwitchEntryStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getLabel", "setLabel", "label", com.github.javaparser.ast.expr.Expression.class, null, true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getStatements", "setStatements", "statements", com.github.javaparser.ast.stmt.Statement.class, null, true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return SwitchEntryStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

