package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodReferenceExprMetaModel extends ClassMetaModel {

    MethodReferenceExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.MethodReferenceExpr.class, "MethodReferenceExpr", "com.github.javaparser.ast.expr.MethodReferenceExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getIdentifier", "setIdentifier", "identifier", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getScope", "setScope", "scope", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeArguments", "setTypeArguments", "typeArguments", int.class, null, true, true, true, false));
    }
}

