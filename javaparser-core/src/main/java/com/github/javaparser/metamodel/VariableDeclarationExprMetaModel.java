package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;

public class VariableDeclarationExprMetaModel extends ClassMetaModel {

    VariableDeclarationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.VariableDeclarationExpr.class, "VariableDeclarationExpr", "com.github.javaparser.ast.expr.VariableDeclarationExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField("annotations"), true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField("modifiers"), true, false, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getVariables", "setVariables", "variables", com.github.javaparser.ast.body.VariableDeclarator.class, getField("variables"), true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return VariableDeclarationExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

