package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;

public interface NodeWithThrowable<N extends Node> {
    N setThrows(NodeList<ReferenceType<?>> throws_);

    NodeList<ReferenceType<?>> getThrows();

    /**
     * Adds this type to the throws clause
     * 
     * @param throwType the exception type
     * @return this
     */
    @SuppressWarnings("unchecked")
    default N addThrows(ReferenceType<?> throwType) {
        getThrows().add(throwType);
        throwType.setParentNode((Node) this);
        return (N) this;
    }

    /**
     * Adds this class to the throws clause
     * 
     * @param clazz the exception class
     * @return this
     */
    default N addThrows(Class<? extends Throwable> clazz) {
        ((Node) this).tryAddImportToParentCompilationUnit(clazz);
        return addThrows(new ClassOrInterfaceType(clazz.getSimpleName()));
    }

    /**
     * Check whether this elements throws this exception class
     * 
     * @param clazz the class of the exception
     * @return true if found in throws clause, false if not
     */
    default boolean isThrows(Class<? extends Throwable> clazz) {
        return isThrows(clazz.getSimpleName());
    }

    /**
     * Check whether this elements throws this exception class
     * 
     * @param throwableName the class of the exception
     * @return true if found in throws clause, false if not
     */
    default boolean isThrows(String throwableName) {
        return getThrows().stream().anyMatch(t -> t.toString().equals(throwableName));
    }
}
