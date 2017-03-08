package com.github.javaparser.metamodel;

import java.util.Optional;

public class ModuleUsesStmtMetaModel extends ModuleStmtMetaModel {

    ModuleUsesStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.modules.ModuleUsesStmt.class, "ModuleUsesStmt", "com.github.javaparser.ast.modules", false, false);
    }

    public PropertyMetaModel typePropertyMetaModel;
}
