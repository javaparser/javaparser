package com.github.javaparser.metamodel;

import java.util.Optional;

public class ThrowStmtMetaModel extends ClassMetaModel {

    ThrowStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ThrowStmt.class, "ThrowStmt", "com.github.javaparser.ast.stmt.ThrowStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExpression", "setExpression", "expression", int.class, null, true, false, false, false));
    }
}

