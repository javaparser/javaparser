package com.github.jmlparser.xpath;

import com.github.javaparser.ast.Node;
import org.jetbrains.annotations.NotNull;
import org.w3c.dom.Element;

import java.util.Collection;

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
public abstract class PseudoAttributeHelper<T extends Node> implements PseudoAttributeProvider {
    private final Class<T> clazz;

    protected PseudoAttributeHelper(Class<T> clazz) {
        this.clazz = clazz;
    }

    @Override
    public final Collection<JPAttrPseudo> attributeForNode(@NotNull Node node, @NotNull Element owner) {
        if (clazz == node.getClass()) {
            return attributes((T) node, owner);
        }
        return null;
    }

    protected abstract Collection<JPAttrPseudo> attributes(@NotNull T node, Element owner);
}
