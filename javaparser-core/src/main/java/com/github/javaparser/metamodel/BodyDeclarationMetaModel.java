package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class BodyDeclarationMetaModel extends ClassMetaModel {

    BodyDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.BodyDeclaration.class, "BodyDeclaration", "com.github.javaparser.ast.body.BodyDeclaration", "com.github.javaparser.ast.body", true);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, null, true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return BodyDeclarationMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

