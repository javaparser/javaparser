package com.github.javaparser.ast;

import javax.lang.model.element.Modifier;
import java.util.Set;

/**
 * A Node with Modifiers.
 * 
 * @since 2.0.1
 */
public interface NodeWithModifiers {
    int getModifiers();
    Set<Modifier> getModifiersSet();
}
