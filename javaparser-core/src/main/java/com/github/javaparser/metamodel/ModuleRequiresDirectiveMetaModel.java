package com.github.javaparser.metamodel;

import java.util.Optional;

public class ModuleRequiresDirectiveMetaModel extends ModuleDirectiveMetaModel {

    ModuleRequiresDirectiveMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.modules.ModuleRequiresDirective.class, "ModuleRequiresDirective", "com.github.javaparser.ast.modules", false, false);
    }

    public PropertyMetaModel modifiersPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;
}
