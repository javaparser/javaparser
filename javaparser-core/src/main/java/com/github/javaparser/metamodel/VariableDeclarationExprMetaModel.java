package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class VariableDeclarationExprMetaModel extends ClassMetaModel {

    VariableDeclarationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.VariableDeclarationExpr.class, "VariableDeclarationExpr", "com.github.javaparser.ast.expr.VariableDeclarationExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, null, true, false, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getVariables", "setVariables", "variables", com.github.javaparser.ast.body.VariableDeclarator.class, null, true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return VariableDeclarationExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

