package com.github.javaparser.ast.nodeTypes;

import java.util.List;

import com.github.javaparser.ast.type.ReferenceType;

public interface NodeWithThrowable<T> {
    T setThrows(List<ReferenceType> throws_);

    List<ReferenceType> getThrows();

    // TODO builder methods
}
