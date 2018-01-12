package com.github.javaparser.ast.nodeTypes;

import java.util.List;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

public interface NodeWithExtends<T> {
    public List<ClassOrInterfaceType> getExtends();

    public T setExtends(final List<ClassOrInterfaceType> extendsList);

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
        getExtends().add(classOrInterfaceType);
        classOrInterfaceType.setParentNode((Node) this);
        return (T) this;
    }
}
