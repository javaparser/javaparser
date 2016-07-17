package com.github.javaparser.ast.nodeTypes;

import java.util.List;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclaratorId;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;

public interface NodeWithParameters<T> {
    List<Parameter> getParameters();

    T setParameters(List<Parameter> parameters);

    @SuppressWarnings("unchecked")
    default T addParameter(Type type, String name) {
        Parameter parameter = new Parameter(type, new VariableDeclaratorId(name));
        getParameters().add(parameter);
        parameter.setParentNode((Node) this);
        return (T) this;
    }

    default T addParameter(Class<?> paramClass, String name) {
        ((Node) this).tryAddImportToParentCompilationUnit(paramClass);
        return addParameter(new ClassOrInterfaceType(paramClass.getSimpleName()), name);
    }

    default Parameter addAndGetParameter(Type type, String name) {
        Parameter parameter = new Parameter(type, new VariableDeclaratorId(name));
        getParameters().add(parameter);
        parameter.setParentNode((Node) this);
        return parameter;
    }

    default Parameter addAndGetParameter(Class<?> paramClass, String name) {
        ((Node) this).tryAddImportToParentCompilationUnit(paramClass);
        return addAndGetParameter(new ClassOrInterfaceType(paramClass.getSimpleName()), name);
    }
}
