package com.github.javaparser.ast.visitor;

public interface Visitable {
    /**
     * Accept method for visitor support.
     *
     * @param <R> the type of the return value of the visitor
     * @param <A> the type the user argument passed to the visitor
     * @param v the visitor implementation
     * @param arg the argument passed to the visitor (of type A)
     * @return the result of the visit (of type R)
     */
    <R, A> R accept(GenericVisitor<R, A> v, A arg);

    /**
     * Accept method for visitor support.
     *
     * @param <A> the type the argument passed for the visitor
     * @param v the visitor implementation
     * @param arg any value relevant for the visitor (of type A)
     */
    <A> void accept(VoidVisitor<A> v, A arg);
}
