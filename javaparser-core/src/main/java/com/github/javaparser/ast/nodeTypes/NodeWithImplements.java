package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

public interface NodeWithImplements<N extends Node> {
    NodeList<ClassOrInterfaceType> getImplements();

    default ClassOrInterfaceType getImplements(int i) {
        return getImplements().get(i);
    }

    N setImplements(NodeList<ClassOrInterfaceType> implementsList);

    /**
     * Add an implements to this
     *
     * @param name the name of the type to extends from
     * @return this
     */
    @SuppressWarnings("unchecked")
    default N addImplements(String name) {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType(name);
        getImplements().add(classOrInterfaceType);
        classOrInterfaceType.setParentNode((Node) this);
        return (N) this;
    }

    /**
     * Add an implements to this and automatically add the import
     *
     * @param clazz the type to implements from
     * @return this
     */
    default N addImplements(Class<?> clazz) {
        ((Node) this).tryAddImportToParentCompilationUnit(clazz);
        return addImplements(clazz.getSimpleName());
    }
}
