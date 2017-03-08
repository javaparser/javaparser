package com.github.javaparser.metamodel;

import java.util.Optional;

public class ModuleRequiresStmtMetaModel extends ModuleStmtMetaModel {

    ModuleRequiresStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.modules.ModuleRequiresStmt.class, "ModuleRequiresStmt", "com.github.javaparser.ast.modules", false, false);
    }

    public PropertyMetaModel modifiersPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;
}
