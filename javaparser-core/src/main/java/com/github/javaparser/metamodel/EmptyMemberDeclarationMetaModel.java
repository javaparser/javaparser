package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class EmptyMemberDeclarationMetaModel extends ClassMetaModel {

    EmptyMemberDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.EmptyMemberDeclaration.class, "EmptyMemberDeclaration", "com.github.javaparser.ast.body.EmptyMemberDeclaration", "com.github.javaparser.ast.body", false);
    }

    private Field getField(String name) {
        try {
            return EmptyMemberDeclarationMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

