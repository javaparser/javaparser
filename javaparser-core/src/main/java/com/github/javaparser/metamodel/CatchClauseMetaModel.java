package com.github.javaparser.metamodel;

import java.util.Optional;

public class CatchClauseMetaModel extends ClassMetaModel {

    CatchClauseMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.CatchClause.class, "CatchClause", "com.github.javaparser.ast.stmt.CatchClause", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getParameter", "setParameter", "parameter", int.class, null, true, false, false, false));
    }
}

