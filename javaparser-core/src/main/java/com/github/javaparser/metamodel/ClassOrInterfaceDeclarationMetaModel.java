package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class ClassOrInterfaceDeclarationMetaModel extends ClassMetaModel {

    ClassOrInterfaceDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class, "ClassOrInterfaceDeclaration", "com.github.javaparser.ast.body.ClassOrInterfaceDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExtendedTypes", "setExtendedTypes", "extendedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getImplementedTypes", "setImplementedTypes", "implementedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "isInterface", "setIsInterface", "isInterface", boolean.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeParameters", "setTypeParameters", "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, null, true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return ClassOrInterfaceDeclarationMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

