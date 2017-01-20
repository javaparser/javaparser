package com.github.javaparser.metamodel;

import java.util.Optional;

public class CatchClauseMetaModel extends BaseNodeMetaModel {

    CatchClauseMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.CatchClause.class, "CatchClause", "com.github.javaparser.ast.stmt.CatchClause", "com.github.javaparser.ast.stmt", false);
    }
}

