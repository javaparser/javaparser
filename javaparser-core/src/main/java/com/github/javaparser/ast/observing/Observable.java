package com.github.javaparser.ast.observing;

public interface Observable<O> {
    void register(O observer);
    void unregister(O observer);
}
