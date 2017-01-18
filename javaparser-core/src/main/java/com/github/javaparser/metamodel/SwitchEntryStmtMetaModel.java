package com.github.javaparser.metamodel;

import java.util.Optional;

public class SwitchEntryStmtMetaModel extends ClassMetaModel {

    SwitchEntryStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.SwitchEntryStmt.class, "SwitchEntryStmt", "com.github.javaparser.ast.stmt.SwitchEntryStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getLabel", "setLabel", "label", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getStatements", "setStatements", "statements", int.class, null, true, false, true, false));
    }
}

