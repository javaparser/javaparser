package com.github.javaparser.metamodel;

import java.util.Optional;

public class ConditionalExprMetaModel extends ClassMetaModel {

    ConditionalExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ConditionalExpr.class, "ConditionalExpr", "com.github.javaparser.ast.expr.ConditionalExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getCondition", "setCondition", "condition", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getElseExpr", "setElseExpr", "elseExpr", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getThenExpr", "setThenExpr", "thenExpr", int.class, null, true, false, false, false));
    }
}

