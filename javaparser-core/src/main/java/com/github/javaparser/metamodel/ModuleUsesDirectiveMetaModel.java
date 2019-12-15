package com.github.javaparser.metamodel;

import java.util.Optional;

public class ModuleUsesDirectiveMetaModel extends ModuleDirectiveMetaModel {

    ModuleUsesDirectiveMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.modules.ModuleUsesDirective.class, "ModuleUsesDirective", "com.github.javaparser.ast.modules", false, false);
    }

    public PropertyMetaModel namePropertyMetaModel;
}
