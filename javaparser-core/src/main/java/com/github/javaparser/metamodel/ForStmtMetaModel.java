package com.github.javaparser.metamodel;

import java.util.Optional;

public class ForStmtMetaModel extends ClassMetaModel {

    ForStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ForStmt.class, "ForStmt", "com.github.javaparser.ast.stmt.ForStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getCompare", "setCompare", "compare", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getInitialization", "setInitialization", "initialization", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getUpdate", "setUpdate", "update", int.class, null, true, false, true, false));
    }
}

