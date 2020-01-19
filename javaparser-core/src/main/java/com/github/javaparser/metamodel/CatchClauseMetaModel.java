package com.github.javaparser.metamodel;

import java.util.Optional;

public class CatchClauseMetaModel extends NodeMetaModel {

    CatchClauseMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.CatchClause.class, "CatchClause", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel parameterPropertyMetaModel;
}
