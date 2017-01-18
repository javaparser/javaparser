package com.github.javaparser.metamodel;

import java.util.Optional;

public class CompilationUnitMetaModel extends ClassMetaModel {

    CompilationUnitMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.CompilationUnit.class, "CompilationUnit", "com.github.javaparser.ast.CompilationUnit", "com.github.javaparser.ast", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getImports", "setImports", "imports", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getPackageDeclaration", "setPackageDeclaration", "packageDeclaration", int.class, null, true, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypes", "setTypes", "types", int.class, null, true, false, true, false));
    }
}

