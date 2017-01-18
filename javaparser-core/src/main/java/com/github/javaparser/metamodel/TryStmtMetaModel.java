package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class TryStmtMetaModel extends ClassMetaModel {

    TryStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.TryStmt.class, "TryStmt", "com.github.javaparser.ast.stmt.TryStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getCatchClauses", "setCatchClauses", "catchClauses", com.github.javaparser.ast.stmt.CatchClause.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getFinallyBlock", "setFinallyBlock", "finallyBlock", com.github.javaparser.ast.stmt.BlockStmt.class, null, true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getResources", "setResources", "resources", com.github.javaparser.ast.expr.VariableDeclarationExpr.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTryBlock", "setTryBlock", "tryBlock", com.github.javaparser.ast.stmt.BlockStmt.class, null, true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return TryStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

