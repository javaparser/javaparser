package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class BlockStmtMetaModel extends ClassMetaModel {

    BlockStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.BlockStmt.class, "BlockStmt", "com.github.javaparser.ast.stmt.BlockStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getStatements", "setStatements", "statements", com.github.javaparser.ast.stmt.Statement.class, null, true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return BlockStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

