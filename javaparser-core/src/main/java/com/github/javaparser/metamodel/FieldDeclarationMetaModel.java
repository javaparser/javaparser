package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class FieldDeclarationMetaModel extends ClassMetaModel {

    FieldDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.FieldDeclaration.class, "FieldDeclaration", "com.github.javaparser.ast.body.FieldDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, null, true, false, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getVariables", "setVariables", "variables", com.github.javaparser.ast.body.VariableDeclarator.class, null, true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return FieldDeclarationMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

