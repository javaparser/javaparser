package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayCreationExprMetaModel extends ClassMetaModel {

    ArrayCreationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ArrayCreationExpr.class, "ArrayCreationExpr", "com.github.javaparser.ast.expr.ArrayCreationExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getElementType", "setElementType", "elementType", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getInitializer", "setInitializer", "initializer", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getLevels", "setLevels", "levels", int.class, null, true, false, true, false));
    }
}

