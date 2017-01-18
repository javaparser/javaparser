package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.ArrayCreationExpr;

public class ArrayCreationExprMetaModel extends ClassMetaModel {

    ArrayCreationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ArrayCreationExpr.class, "ArrayCreationExpr", "com.github.javaparser.ast.expr.ArrayCreationExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getElementType", "setElementType", "elementType", com.github.javaparser.ast.type.Type.class, getField("elementType"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getInitializer", "setInitializer", "initializer", com.github.javaparser.ast.expr.ArrayInitializerExpr.class, getField("initializer"), true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getLevels", "setLevels", "levels", com.github.javaparser.ast.ArrayCreationLevel.class, getField("levels"), true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return ArrayCreationExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

