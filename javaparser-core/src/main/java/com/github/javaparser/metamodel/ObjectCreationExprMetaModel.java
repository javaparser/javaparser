package com.github.javaparser.metamodel;

import java.util.Optional;

public class ObjectCreationExprMetaModel extends ClassMetaModel {

    public ObjectCreationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.ObjectCreationExpr.class, "ObjectCreationExpr", "com.github.javaparser.ast.expr.ObjectCreationExpr", "com.github.javaparser.ast.expr", false);
    }
}

