package com.github.javaparser.metamodel;

import java.util.Optional;

public class AssertStmtMetaModel extends ClassMetaModel {

    AssertStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.AssertStmt.class, "AssertStmt", "com.github.javaparser.ast.stmt.AssertStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getCheck", "setCheck", "check", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getMessage", "setMessage", "message", int.class, null, true, false, false, false));
    }
}

