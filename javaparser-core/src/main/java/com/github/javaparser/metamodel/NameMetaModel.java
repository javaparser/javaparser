package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.Name;

public class NameMetaModel extends ClassMetaModel {

    NameMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.Name.class, "Name", "com.github.javaparser.ast.expr.Name", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getIdentifier", "setIdentifier", "identifier", java.lang.String.class, getField("identifier"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getQualifier", "setQualifier", "qualifier", com.github.javaparser.ast.expr.Name.class, getField("qualifier"), true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return Name.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

