package com.github.javaparser.metamodel;

import java.util.Optional;

public class ModuleOpensDirectiveMetaModel extends ModuleDirectiveMetaModel {

    ModuleOpensDirectiveMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.modules.ModuleOpensDirective.class, "ModuleOpensDirective", "com.github.javaparser.ast.modules", false, false);
    }

    public PropertyMetaModel moduleNamesPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;
}
