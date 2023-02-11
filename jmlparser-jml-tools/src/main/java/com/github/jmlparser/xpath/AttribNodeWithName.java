package com.github.jmlparser.xpath;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.w3c.dom.Element;

import java.util.Collection;
import java.util.Collections;

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
public class AttribNodeWithName implements PseudoAttributeProvider {
    @Override
    public @Nullable Collection<JPAttrPseudo> attributeForNode(@NotNull Node node, @NotNull Element owner) {
        if (node instanceof NodeWithName<?> n) {
            return Collections.singleton(new JPAttrPseudo("name", n::getNameAsString, owner));
        }
        return null;
    }
}
