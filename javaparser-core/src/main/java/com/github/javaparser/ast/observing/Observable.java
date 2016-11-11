package com.github.javaparser.ast.observing;

public interface Observable {
    void register(Observer observer);
    void unregister(Observer observer);
}
