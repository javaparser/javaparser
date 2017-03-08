package com.github.javaparser.metamodel;

import java.util.Optional;
import com.github.javaparser.ast.Node;

public class StatementMetaModel extends NodeMetaModel {

    StatementMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.Statement.class, "Statement", "com.github.javaparser.ast.stmt", true, false);
    }

    protected StatementMetaModel(Optional<BaseNodeMetaModel> superNodeMetaModel, Class<? extends Node> type, String name, String packageName, boolean isAbstract, boolean hasWildcard) {
        super(superNodeMetaModel, type, name, packageName, isAbstract, hasWildcard);
    }
}
