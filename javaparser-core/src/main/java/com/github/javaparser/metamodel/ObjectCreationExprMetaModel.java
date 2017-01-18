package com.github.javaparser.metamodel;

import java.util.Optional;

public class ObjectCreationExprMetaModel extends ClassMetaModel {

    ObjectCreationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ObjectCreationExpr.class, "ObjectCreationExpr", "com.github.javaparser.ast.expr.ObjectCreationExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnonymousClassBody", "setAnonymousClassBody", "anonymousClassBody", int.class, null, true, true, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getArguments", "setArguments", "arguments", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getScope", "setScope", "scope", int.class, null, true, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeArguments", "setTypeArguments", "typeArguments", int.class, null, true, true, true, false));
    }
}

