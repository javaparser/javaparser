package com.github.javaparser.metamodel;

import java.util.Optional;

public class ModuleOpensStmtMetaModel extends ModuleStmtMetaModel {

    ModuleOpensStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.modules.ModuleOpensStmt.class, "ModuleOpensStmt", "com.github.javaparser.ast.modules", false, false);
    }

    public PropertyMetaModel moduleNamesPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;
}
