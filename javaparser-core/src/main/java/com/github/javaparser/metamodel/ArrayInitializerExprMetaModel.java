package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayInitializerExprMetaModel extends ClassMetaModel {

    ArrayInitializerExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ArrayInitializerExpr.class, "ArrayInitializerExpr", "com.github.javaparser.ast.expr.ArrayInitializerExpr", "com.github.javaparser.ast.expr", false);
    }
}

