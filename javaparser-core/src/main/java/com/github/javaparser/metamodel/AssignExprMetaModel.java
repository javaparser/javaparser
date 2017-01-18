package com.github.javaparser.metamodel;

import java.util.Optional;

public class AssignExprMetaModel extends ClassMetaModel {

    AssignExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.AssignExpr.class, "AssignExpr", "com.github.javaparser.ast.expr.AssignExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getOperator", "setOperator", "operator", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTarget", "setTarget", "target", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getValue", "setValue", "value", int.class, null, true, false, false, false));
    }
}

