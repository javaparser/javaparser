package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class NameMetaModel extends ClassMetaModel {

    NameMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.Name.class, "Name", "com.github.javaparser.ast.expr.Name", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getIdentifier", "setIdentifier", "identifier", java.lang.String.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getQualifier", "setQualifier", "qualifier", com.github.javaparser.ast.expr.Name.class, null, true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return NameMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

