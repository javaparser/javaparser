package com.github.javaparser.model;

import java.util.List;
import java.util.Optional;

public interface ClassMetaModel {
    Optional<OldClassMetaModel> getSuperClassMetaModel();

    JavaParserMetaModel getJavaParserMetaModel();

    List<FieldMetaModel> getFieldMetaModels();

    Class<?> getReflectionClass();

    String getClassName();

    String getQualifiedClassName();

    String getPackageName();

    boolean isAbstract();

    Flags getFlags();
}
