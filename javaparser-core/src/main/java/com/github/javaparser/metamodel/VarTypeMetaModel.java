package com.github.javaparser.metamodel;

import java.util.Optional;

public class VarTypeMetaModel extends TypeMetaModel {

    VarTypeMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.type.VarType.class, "VarType", "com.github.javaparser.ast.type", false, false);
    }
}
