package com.github.javaparser.metamodel;

import java.util.Optional;

public class CatchClauseMetaModel extends BaseNodeMetaModel {

    CatchClauseMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.CatchClause.class, "CatchClause", "com.github.javaparser.ast.stmt.CatchClause", "com.github.javaparser.ast.stmt", false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel parameterPropertyMetaModel;
}

