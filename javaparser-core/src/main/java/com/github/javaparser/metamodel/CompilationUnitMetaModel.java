package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class CompilationUnitMetaModel extends ClassMetaModel {

    CompilationUnitMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.CompilationUnit.class, "CompilationUnit", "com.github.javaparser.ast.CompilationUnit", "com.github.javaparser.ast", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getImports", "setImports", "imports", com.github.javaparser.ast.ImportDeclaration.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getPackageDeclaration", "setPackageDeclaration", "packageDeclaration", com.github.javaparser.ast.PackageDeclaration.class, null, true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypes", "setTypes", "types", com.github.javaparser.ast.body.TypeDeclaration.class, null, true, false, true, false, true));
    }

    private Field getField(String name) {
        try {
            return CompilationUnitMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

