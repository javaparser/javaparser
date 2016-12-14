package com.github.javaparser.ast.observer;

/**
 * Observable element.
 */
public interface Observable {

    /**
     * Register an observer.
     */
    void register(AstObserver observer);

    /**
     * Unregister an observer. If the given observer was not registered there are no effects.
     */
    void unregister(AstObserver observer);

    /**
     * Was this observer registered?
     * Note that equals is used to determine if the given observer was registered.
     */
    boolean isRegistered(AstObserver observer);
}
