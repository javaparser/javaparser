package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

import java.util.List;

public interface NodeWithImplements<T> {
    public List<ClassOrInterfaceType> getImplementsList();

    public T setImplementsList(List<ClassOrInterfaceType> implementsList);

    /**
     * Add an implements to this
     * 
     * @param name the name of the type to extends from
     * @return this
     */
    @SuppressWarnings("unchecked")
    public default T addImplements(String name) {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType(name);
        getImplementsList().add(classOrInterfaceType);
        classOrInterfaceType.setParentNode((Node) this);
        return (T) this;
    }

    /**
     * Add an implements to this and automatically add the import
     * 
     * @param clazz the type to implements from
     * @return this
     */
    public default T addImplements(Class<?> clazz) {
        ((Node) this).tryAddImportToParentCompilationUnit(clazz);
        return addImplements(clazz.getSimpleName());
    }
}
