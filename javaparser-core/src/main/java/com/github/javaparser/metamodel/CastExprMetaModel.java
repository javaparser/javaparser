package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class CastExprMetaModel extends ClassMetaModel {

    CastExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.CastExpr.class, "CastExpr", "com.github.javaparser.ast.expr.CastExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return CastExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

