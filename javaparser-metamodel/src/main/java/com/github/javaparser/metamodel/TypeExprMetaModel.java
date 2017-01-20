package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeExprMetaModel extends ClassMetaModel {

    TypeExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.TypeExpr.class, "TypeExpr", "com.github.javaparser.ast.expr.TypeExpr", "com.github.javaparser.ast.expr", false);
    }
}

