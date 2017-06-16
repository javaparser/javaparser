package com.github.javaparser.metamodel;

import java.util.Optional;

public class ModuleProvidesStmtMetaModel extends ModuleStmtMetaModel {

    ModuleProvidesStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.modules.ModuleProvidesStmt.class, "ModuleProvidesStmt", "com.github.javaparser.ast.modules", false, false);
    }

    public PropertyMetaModel typePropertyMetaModel;

    public PropertyMetaModel withTypesPropertyMetaModel;
}
