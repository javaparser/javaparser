package com.github.javaparser.metamodel;

import java.util.Optional;

public class ForeachStmtMetaModel extends ClassMetaModel {

    ForeachStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ForeachStmt.class, "ForeachStmt", "com.github.javaparser.ast.stmt.ForeachStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getIterable", "setIterable", "iterable", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getVariable", "setVariable", "variable", int.class, null, true, false, false, false));
    }
}

