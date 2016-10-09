package com.github.javaparser.ast.nodeTypes;

import java.util.List;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

public interface NodeWithImplements<T> {
    List<ClassOrInterfaceType> getImplements();

    T setImplements(List<ClassOrInterfaceType> implementsList);

    /**
     * Add an implements to this
     * 
     * @param name the name of the type to extends from
     * @return this
     */
    @SuppressWarnings("unchecked")
    default T addImplements(String name) {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType(name);
        getImplements().add(classOrInterfaceType);
        classOrInterfaceType.setParentNode((Node) this);
        return (T) this;
    }

    /**
     * Add an implements to this and automatically add the import
     * 
     * @param clazz the type to implements from
     * @return this
     */
    default T addImplements(Class<?> clazz) {
        ((Node) this).tryAddImportToParentCompilationUnit(clazz);
        return addImplements(clazz.getSimpleName());
    }
}
