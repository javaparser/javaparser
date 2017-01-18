package com.github.javaparser.metamodel;

import java.util.Optional;

public class SingleMemberAnnotationExprMetaModel extends ClassMetaModel {

    SingleMemberAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.SingleMemberAnnotationExpr.class, "SingleMemberAnnotationExpr", "com.github.javaparser.ast.expr.SingleMemberAnnotationExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getMemberValue", "setMemberValue", "memberValue", int.class, null, true, false, false, false));
    }
}

