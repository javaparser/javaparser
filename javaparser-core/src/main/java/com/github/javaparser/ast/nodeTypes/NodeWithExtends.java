package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

public interface NodeWithExtends<N extends Node> {
    NodeList<ClassOrInterfaceType> getExtends();

    default ClassOrInterfaceType getExtends(int i) {
        return getExtends().get(i);
    }

    N setExtends(NodeList<ClassOrInterfaceType> extendsList);

    /**
     * Add an extends to this and automatically add the import
     * 
     * @param clazz the class to extand from
     * @return this
     */
    default N addExtends(Class<?> clazz) {
        ((Node) this).tryAddImportToParentCompilationUnit(clazz);
        return addExtends(clazz.getSimpleName());
    }

    /**
     * Add an extends to this
     * 
     * @param name the name of the type to extends from
     * @return this
     */
    @SuppressWarnings("unchecked")
    default N addExtends(String name) {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType(name);
        getExtends().add(classOrInterfaceType);
        classOrInterfaceType.setParentNode((Node) this);
        return (N) this;
    }
}
