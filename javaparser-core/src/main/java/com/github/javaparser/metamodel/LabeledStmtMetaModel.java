package com.github.javaparser.metamodel;

import java.util.Optional;

public class LabeledStmtMetaModel extends ClassMetaModel {

    LabeledStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.LabeledStmt.class, "LabeledStmt", "com.github.javaparser.ast.stmt.LabeledStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getLabel", "setLabel", "label", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getStatement", "setStatement", "statement", int.class, null, true, false, false, false));
    }
}

