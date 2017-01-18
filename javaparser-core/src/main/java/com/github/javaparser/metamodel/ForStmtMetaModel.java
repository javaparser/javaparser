package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class ForStmtMetaModel extends ClassMetaModel {

    ForStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ForStmt.class, "ForStmt", "com.github.javaparser.ast.stmt.ForStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getCompare", "setCompare", "compare", com.github.javaparser.ast.expr.Expression.class, null, true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getInitialization", "setInitialization", "initialization", com.github.javaparser.ast.expr.Expression.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getUpdate", "setUpdate", "update", com.github.javaparser.ast.expr.Expression.class, null, true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return ForStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

