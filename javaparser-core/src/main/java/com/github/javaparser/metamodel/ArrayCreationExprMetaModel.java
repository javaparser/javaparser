package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayCreationExprMetaModel extends ClassMetaModel {

    public ArrayCreationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.ArrayCreationExpr.class, "ArrayCreationExpr", "com.github.javaparser.ast.expr.ArrayCreationExpr", "com.github.javaparser.ast.expr", false);
    }
}

