package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.stmt.CatchClause;

public class CatchClauseMetaModel extends ClassMetaModel {

    CatchClauseMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.CatchClause.class, "CatchClause", "com.github.javaparser.ast.stmt.CatchClause", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField("body"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getParameter", "setParameter", "parameter", com.github.javaparser.ast.body.Parameter.class, getField("parameter"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return CatchClause.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

