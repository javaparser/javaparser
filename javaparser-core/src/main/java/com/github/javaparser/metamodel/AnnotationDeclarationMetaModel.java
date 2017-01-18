package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.body.AnnotationDeclaration;

public class AnnotationDeclarationMetaModel extends ClassMetaModel {

    AnnotationDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.AnnotationDeclaration.class, "AnnotationDeclaration", "com.github.javaparser.ast.body.AnnotationDeclaration", "com.github.javaparser.ast.body", false);
    }

    private Field getField(String name) {
        try {
            return AnnotationDeclaration.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

