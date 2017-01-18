package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;

public class AnnotationMemberDeclarationMetaModel extends ClassMetaModel {

    AnnotationMemberDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.AnnotationMemberDeclaration.class, "AnnotationMemberDeclaration", "com.github.javaparser.ast.body.AnnotationMemberDeclaration", "com.github.javaparser.ast.body", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getDefaultValue", "setDefaultValue", "defaultValue", com.github.javaparser.ast.expr.Expression.class, getField("defaultValue"), true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField("modifiers"), true, false, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField("name"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField("type"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return AnnotationMemberDeclaration.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

