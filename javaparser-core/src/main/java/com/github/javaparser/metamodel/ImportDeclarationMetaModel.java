package com.github.javaparser.metamodel;

import java.util.Optional;

public class ImportDeclarationMetaModel extends ClassMetaModel {

    ImportDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.ImportDeclaration.class, "ImportDeclaration", "com.github.javaparser.ast.ImportDeclaration", "com.github.javaparser.ast", false);
        fieldMetaModels.add(new FieldMetaModel(this, "isAsterisk", "setIsAsterisk", "isAsterisk", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "isStatic", "setIsStatic", "isStatic", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", int.class, null, true, false, false, false));
    }
}

