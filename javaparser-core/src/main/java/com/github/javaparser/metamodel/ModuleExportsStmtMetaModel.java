package com.github.javaparser.metamodel;

import java.util.Optional;

public class ModuleExportsStmtMetaModel extends ModuleStmtMetaModel {

    ModuleExportsStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.modules.ModuleExportsStmt.class, "ModuleExportsStmt", "com.github.javaparser.ast.modules", false, false);
    }

    public PropertyMetaModel moduleNamesPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;
}
