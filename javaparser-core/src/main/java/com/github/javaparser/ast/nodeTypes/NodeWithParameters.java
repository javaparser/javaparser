package com.github.javaparser.ast.nodeTypes;

import java.util.List;

import com.github.javaparser.ast.body.Parameter;

public interface NodeWithParameters<T> {
    List<Parameter> getParameters();

    T setParameters(List<Parameter> parameters);

    // TODO builder methods
}
