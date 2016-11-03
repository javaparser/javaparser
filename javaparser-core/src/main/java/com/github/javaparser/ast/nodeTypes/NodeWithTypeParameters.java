package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.TypeParameter;

/**
 * A node that can have type parameters.
 * <pre>
 *     class X {}        --> typeParameters == []
 *     class X&lt;> {}      --> does not occur.
 *     class X&lt;C,D> {}   --> typeParameters = [C,D] 
 * </pre>
 */
public interface NodeWithTypeParameters<T extends Node> {
    NodeList<TypeParameter> getTypeParameters();

    T setTypeParameters(NodeList<TypeParameter> typeParameters);

    default boolean isGeneric() {
        return getTypeParameters().size() > 0;
    }
}
