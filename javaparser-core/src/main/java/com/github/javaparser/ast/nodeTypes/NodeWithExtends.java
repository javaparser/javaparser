package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

import java.util.List;

public interface NodeWithExtends<T> {
    public List<ClassOrInterfaceType> getExtendsList();

    public T setExtendsList(final List<ClassOrInterfaceType> extendsList);

    /**
     * Add an extends to this and automatically add the import
     * 
     * @param clazz the class to extand from
     * @return this
     */
    public default T addExtends(Class<?> clazz) {
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
    public default T addExtends(String name) {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType(name);
        getExtendsList().add(classOrInterfaceType);
        classOrInterfaceType.setParentNode((Node) this);
        return (T) this;
    }
}
