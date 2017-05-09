package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.SimpleName;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNonEmpty;

/**
 * A node that has an optional label.
 */
public interface NodeWithOptionalLabel<T extends Node> {
    Optional<SimpleName> getLabel();

    T setLabel(SimpleName label);
    
    T removeLabel();

    default T setLabel(String label) {
        assertNonEmpty(label);
        return setLabel(new SimpleName(label));
    }

    default Optional<String> getLabelAsString() {
        return getLabel().flatMap(l -> Optional.of(l.getIdentifier()));
    }
}
