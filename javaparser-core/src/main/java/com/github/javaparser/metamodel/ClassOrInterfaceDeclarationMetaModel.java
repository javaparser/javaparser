package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;

public class ClassOrInterfaceDeclarationMetaModel extends ClassMetaModel {

    ClassOrInterfaceDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class, "ClassOrInterfaceDeclaration", "com.github.javaparser.ast.body.ClassOrInterfaceDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExtendedTypes", "setExtendedTypes", "extendedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField("extendedTypes"), true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getImplementedTypes", "setImplementedTypes", "implementedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField("implementedTypes"), true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "isInterface", "setIsInterface", "isInterface", boolean.class, getField("isInterface"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeParameters", "setTypeParameters", "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, getField("typeParameters"), true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return ClassOrInterfaceDeclaration.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

