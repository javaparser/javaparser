package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.stmt.BlockStmt;

public class BlockStmtMetaModel extends ClassMetaModel {

    BlockStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.BlockStmt.class, "BlockStmt", "com.github.javaparser.ast.stmt.BlockStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getStatements", "setStatements", "statements", com.github.javaparser.ast.stmt.Statement.class, getField("statements"), true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return BlockStmt.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

