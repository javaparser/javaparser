package com.github.javaparser.metamodel;

import java.util.Optional;

public class IfStmtMetaModel extends ClassMetaModel {

    IfStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.IfStmt.class, "IfStmt", "com.github.javaparser.ast.stmt.IfStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getCondition", "setCondition", "condition", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getElseStmt", "setElseStmt", "elseStmt", int.class, null, true, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getThenStmt", "setThenStmt", "thenStmt", int.class, null, true, false, false, false));
    }
}

