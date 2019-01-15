package com.github.javaparser.metamodel;

import java.util.Optional;

public class SwitchEntryMetaModel extends NodeMetaModel {

    SwitchEntryMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.SwitchEntry.class, "SwitchEntry", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel labelPropertyMetaModel;

    public PropertyMetaModel statementsPropertyMetaModel;
}
