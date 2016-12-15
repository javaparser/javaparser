package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;

public interface NodeWithThrownExceptions<N extends Node> {
    N setThrownExceptions(NodeList<ReferenceType> thrownExceptions);

    NodeList<ReferenceType> getThrownExceptions();

    default ReferenceType getThrownException(int i) {
        return getThrownExceptions().get(i);
    }

    /**
     * Adds this type to the throws clause
     *
     * @param throwType the exception type
     * @return this
     */
    @SuppressWarnings("unchecked")
    default N addThrownException(ReferenceType throwType) {
        getThrownExceptions().add(throwType);
        throwType.setParentNode((Node) this);
        return (N) this;
    }

    /**
     * Adds this class to the throws clause
     *
     * @param clazz the exception class
     * @return this
     */
    default N addThrownException(Class<? extends Throwable> clazz) {
        ((Node) this).tryAddImportToParentCompilationUnit(clazz);
        return addThrownException(new ClassOrInterfaceType(clazz.getSimpleName()));
    }

    /**
     * Check whether this elements throws this exception class.
     * Note that this is simply a text compare of the simple name of the class,
     * no actual type resolution takes place.
     *
     * @param clazz the class of the exception
     * @return true if found in throws clause, false if not
     */
    default boolean isThrown(Class<? extends Throwable> clazz) {
        return isThrown(clazz.getSimpleName());
    }

    /**
     * Check whether this elements throws this exception class
     * Note that this is simply a text compare,
     * no actual type resolution takes place.
     *
     * @param throwableName the class of the exception
     * @return true if found in throws clause, false if not
     */
    default boolean isThrown(String throwableName) {
        return getThrownExceptions().stream().anyMatch(t -> t.toString().equals(throwableName));
    }
}
