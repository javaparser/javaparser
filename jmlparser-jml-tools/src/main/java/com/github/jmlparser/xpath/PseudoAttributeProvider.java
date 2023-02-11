package com.github.jmlparser.xpath;

import com.github.javaparser.ast.Node;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.w3c.dom.Element;

import java.util.Collection;

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
public interface PseudoAttributeProvider {
    @Nullable
    Collection<JPAttrPseudo> attributeForNode(@NotNull Node node, @NotNull Element owner);
}
