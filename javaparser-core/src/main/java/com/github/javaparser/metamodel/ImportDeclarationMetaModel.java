package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.ImportDeclaration;

public class ImportDeclarationMetaModel extends ClassMetaModel {

    ImportDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.ImportDeclaration.class, "ImportDeclaration", "com.github.javaparser.ast.ImportDeclaration", "com.github.javaparser.ast", false);
        fieldMetaModels.add(new FieldMetaModel(this, "isAsterisk", "setIsAsterisk", "isAsterisk", boolean.class, getField("isAsterisk"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "isStatic", "setIsStatic", "isStatic", boolean.class, getField("isStatic"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.Name.class, getField("name"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ImportDeclaration.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

