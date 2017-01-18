package com.github.javaparser.metamodel;

import java.util.Optional;

public class TryStmtMetaModel extends ClassMetaModel {

    TryStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.TryStmt.class, "TryStmt", "com.github.javaparser.ast.stmt.TryStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getCatchClauses", "setCatchClauses", "catchClauses", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getFinallyBlock", "setFinallyBlock", "finallyBlock", int.class, null, true, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getResources", "setResources", "resources", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTryBlock", "setTryBlock", "tryBlock", int.class, null, true, true, false, false));
    }
}

