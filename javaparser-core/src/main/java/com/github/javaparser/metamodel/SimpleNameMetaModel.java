package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.SimpleName;

public class SimpleNameMetaModel extends ClassMetaModel {

    SimpleNameMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.SimpleName.class, "SimpleName", "com.github.javaparser.ast.expr.SimpleName", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getIdentifier", "setIdentifier", "identifier", java.lang.String.class, getField("identifier"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return SimpleName.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

