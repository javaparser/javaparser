package com.github.javaparser.metamodel;

import java.util.Optional;

public class MemberValuePairMetaModel extends ClassMetaModel {

    MemberValuePairMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.MemberValuePair.class, "MemberValuePair", "com.github.javaparser.ast.expr.MemberValuePair", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getValue", "setValue", "value", int.class, null, true, false, false, false));
    }
}

