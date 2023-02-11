package com.github.jmlparser.xpath;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.w3c.dom.Element;

import java.util.Arrays;
import java.util.Collection;

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
public class AttribModifier implements PseudoAttributeProvider {
    @Override
    public @Nullable Collection<JPAttrPseudo> attributeForNode(@NotNull Node node, @NotNull Element owner) {
        if (node instanceof NodeWithModifiers<?> m) {
            return Arrays.stream(Modifier.DefaultKeyword.values()).map(
                    it -> new JPAttrPseudo(it.name(), () -> "" + m.hasModifier(it), owner)).toList();
        }
        return null;
    }
}
