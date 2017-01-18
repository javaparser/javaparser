package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class PackageDeclarationMetaModel extends ClassMetaModel {

    PackageDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.PackageDeclaration.class, "PackageDeclaration", "com.github.javaparser.ast.PackageDeclaration", "com.github.javaparser.ast", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.Name.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return PackageDeclarationMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

