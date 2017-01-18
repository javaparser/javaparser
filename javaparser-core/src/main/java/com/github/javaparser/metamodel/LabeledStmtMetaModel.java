package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.stmt.LabeledStmt;

public class LabeledStmtMetaModel extends ClassMetaModel {

    LabeledStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.LabeledStmt.class, "LabeledStmt", "com.github.javaparser.ast.stmt.LabeledStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getLabel", "setLabel", "label", com.github.javaparser.ast.expr.SimpleName.class, getField("label"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getStatement", "setStatement", "statement", com.github.javaparser.ast.stmt.Statement.class, getField("statement"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return LabeledStmt.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

