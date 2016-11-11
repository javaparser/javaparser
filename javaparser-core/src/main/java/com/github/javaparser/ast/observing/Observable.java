package com.github.javaparser.ast.observing;

public interface Observable {
    void register(AstObserver observer);
    void unregister(AstObserver observer);
    boolean isRegistered(AstObserver observer);
}
