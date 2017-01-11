package com.github.javaparser.metamodel;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public class JavaParserMetaModel {
    private List<ClassMetaModel> classMetaModels = new ArrayList<>();

    public List<ClassMetaModel> getClassMetaModels() {
        return classMetaModels;
    }

    public Optional<ClassMetaModel> getClassMetaModel(Class<?> c) {
        for (ClassMetaModel oldClassMetaModel : classMetaModels) {
            if (oldClassMetaModel.className.equals(c.getSimpleName())) {
                return Optional.of(oldClassMetaModel);
            }
        }
        return Optional.empty();
    }

    @Override
    public String toString() {
        StringBuilder b = new StringBuilder();
        for (ClassMetaModel oldClassMetaModel : getClassMetaModels()) {
            b.append(oldClassMetaModel).append("\n");
            for (FieldMetaModel oldFieldMetaModel : oldClassMetaModel.fieldMetaModels) {
                b.append("\t").append(oldFieldMetaModel).append("\n");
            }
        }
        return b.toString();
    }
}
