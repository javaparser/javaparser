package com.github.javaparser.resolution;

import com.github.javaparser.ast.Node;

public interface SymbolResolver {
    <T> T resolve(Node node, Class<T> resultClass);
}
