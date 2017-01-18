package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassOrInterfaceDeclarationMetaModel extends ClassMetaModel {

    ClassOrInterfaceDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class, "ClassOrInterfaceDeclaration", "com.github.javaparser.ast.body.ClassOrInterfaceDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExtendedTypes", "setExtendedTypes", "extendedTypes", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getImplementedTypes", "setImplementedTypes", "implementedTypes", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getIsInterface", "setIsInterface", "isInterface", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeParameters", "setTypeParameters", "typeParameters", int.class, null, true, false, true, false));
    }
}

