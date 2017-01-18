package com.github.javaparser.metamodel;

import java.util.Optional;

public class WhileStmtMetaModel extends ClassMetaModel {

    WhileStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.WhileStmt.class, "WhileStmt", "com.github.javaparser.ast.stmt.WhileStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getCondition", "setCondition", "condition", int.class, null, true, false, false, false));
    }
}

