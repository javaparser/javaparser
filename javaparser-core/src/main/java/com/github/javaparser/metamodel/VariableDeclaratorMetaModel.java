package com.github.javaparser.metamodel;

import java.util.Optional;

public class VariableDeclaratorMetaModel extends ClassMetaModel {

    VariableDeclaratorMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.VariableDeclarator.class, "VariableDeclarator", "com.github.javaparser.ast.body.VariableDeclarator", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getInitializer", "setInitializer", "initializer", int.class, null, true, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", int.class, null, true, false, false, false));
    }
}

