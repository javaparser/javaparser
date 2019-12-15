package com.github.javaparser.metamodel;

import java.util.Optional;

public class ModuleExportsDirectiveMetaModel extends ModuleDirectiveMetaModel {

    ModuleExportsDirectiveMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.modules.ModuleExportsDirective.class, "ModuleExportsDirective", "com.github.javaparser.ast.modules", false, false);
    }

    public PropertyMetaModel moduleNamesPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;
}
