package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.body.EnumDeclaration;

public class EnumDeclarationMetaModel extends ClassMetaModel {

    EnumDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.EnumDeclaration.class, "EnumDeclaration", "com.github.javaparser.ast.body.EnumDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getEntries", "setEntries", "entries", com.github.javaparser.ast.body.EnumConstantDeclaration.class, getField("entries"), true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getImplementedTypes", "setImplementedTypes", "implementedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField("implementedTypes"), true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return EnumDeclaration.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

