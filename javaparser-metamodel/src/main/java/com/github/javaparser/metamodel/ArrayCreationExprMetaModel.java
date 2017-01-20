package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayCreationExprMetaModel extends BaseNodeMetaModel {

    ArrayCreationExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ArrayCreationExpr.class, "ArrayCreationExpr", "com.github.javaparser.ast.expr.ArrayCreationExpr", "com.github.javaparser.ast.expr", false);
    }
}

