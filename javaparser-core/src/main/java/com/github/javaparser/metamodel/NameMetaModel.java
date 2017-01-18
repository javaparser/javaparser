package com.github.javaparser.metamodel;

import java.util.Optional;

public class NameMetaModel extends ClassMetaModel {

    NameMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.Name.class, "Name", "com.github.javaparser.ast.expr.Name", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getIdentifier", "setIdentifier", "identifier", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getQualifier", "setQualifier", "qualifier", int.class, null, true, false, false, false));
    }
}

