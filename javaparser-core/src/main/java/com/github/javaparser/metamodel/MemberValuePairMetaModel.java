package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.MemberValuePair;

public class MemberValuePairMetaModel extends ClassMetaModel {

    MemberValuePairMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.MemberValuePair.class, "MemberValuePair", "com.github.javaparser.ast.expr.MemberValuePair", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField("name"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getValue", "setValue", "value", com.github.javaparser.ast.expr.Expression.class, getField("value"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return MemberValuePair.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

