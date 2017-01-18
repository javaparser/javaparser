package com.github.javaparser.metamodel;

import java.util.Optional;

public class LambdaExprMetaModel extends ClassMetaModel {

    LambdaExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.LambdaExpr.class, "LambdaExpr", "com.github.javaparser.ast.expr.LambdaExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getIsEnclosingParameters", "setIsEnclosingParameters", "isEnclosingParameters", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getParameters", "setParameters", "parameters", int.class, null, true, false, true, false));
    }
}

