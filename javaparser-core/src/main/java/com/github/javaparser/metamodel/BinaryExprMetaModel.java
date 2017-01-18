package com.github.javaparser.metamodel;

import java.util.Optional;

public class BinaryExprMetaModel extends ClassMetaModel {

    BinaryExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.BinaryExpr.class, "BinaryExpr", "com.github.javaparser.ast.expr.BinaryExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getLeft", "setLeft", "left", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getOperator", "setOperator", "operator", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getRight", "setRight", "right", int.class, null, true, false, false, false));
    }
}

