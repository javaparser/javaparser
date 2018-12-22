package com.github.javaparser.metamodel;

import java.util.Optional;

public class ModifierMetaModel extends NodeMetaModel {

    ModifierMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.Modifier.class, "Modifier", "com.github.javaparser.ast", false, false);
    }

    public PropertyMetaModel keywordPropertyMetaModel;
}
