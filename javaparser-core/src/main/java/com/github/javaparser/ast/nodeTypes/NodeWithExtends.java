package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

public interface NodeWithExtends<T extends Node> {
    NodeList<ClassOrInterfaceType> getExtends();

    T setExtends(NodeList<ClassOrInterfaceType> extendsList);

    /**
     * Add an extends to this and automatically add the import
     * 
     * @param clazz the class to extand from
     * @return this
     */
    default T addExtends(Class<?> clazz) {
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
    default T addExtends(String name) {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType(name);
        getExtends().add(classOrInterfaceType);
        classOrInterfaceType.setParentNode((Node) this);
        return (T) this;
    }
}
