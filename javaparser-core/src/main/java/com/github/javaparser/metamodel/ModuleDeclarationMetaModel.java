package com.github.javaparser.metamodel;

import java.util.Optional;

public class ModuleDeclarationMetaModel extends NodeMetaModel {

    ModuleDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.modules.ModuleDeclaration.class, "ModuleDeclaration", "com.github.javaparser.ast.modules", false, false);
    }

    public PropertyMetaModel annotationsPropertyMetaModel;

    public PropertyMetaModel directivesPropertyMetaModel;

    public PropertyMetaModel isOpenPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;
}
