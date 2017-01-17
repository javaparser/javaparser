package com.github.javaparser.metamodel;

import java.util.Optional;

public class NameMetaModel extends ClassMetaModel {

    public NameMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.Name.class, "Name", "com.github.javaparser.ast.expr.Name", "com.github.javaparser.ast.expr", false);
    }
}

