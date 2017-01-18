package com.github.javaparser.metamodel;

import java.util.Optional;

public class BooleanLiteralExprMetaModel extends ClassMetaModel {

    BooleanLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.BooleanLiteralExpr.class, "BooleanLiteralExpr", "com.github.javaparser.ast.expr.BooleanLiteralExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getValue", "setValue", "value", int.class, null, true, false, false, false));
    }
}

