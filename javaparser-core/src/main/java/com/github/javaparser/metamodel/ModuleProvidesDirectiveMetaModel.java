package com.github.javaparser.metamodel;

import java.util.Optional;

public class ModuleProvidesDirectiveMetaModel extends ModuleDirectiveMetaModel {

    ModuleProvidesDirectiveMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.modules.ModuleProvidesDirective.class, "ModuleProvidesDirective", "com.github.javaparser.ast.modules", false, false);
    }

    public PropertyMetaModel namePropertyMetaModel;

    public PropertyMetaModel withPropertyMetaModel;
}
