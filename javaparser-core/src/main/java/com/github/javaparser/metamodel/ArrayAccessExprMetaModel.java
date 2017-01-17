package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayAccessExprMetaModel extends ClassMetaModel {

    public ArrayAccessExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.ArrayAccessExpr.class, "ArrayAccessExpr", "com.github.javaparser.ast.expr.ArrayAccessExpr", "com.github.javaparser.ast.expr", false);
    }
}

