package io.github.jmltoolkit.xpath

import com.github.javaparser.ast.Modifier.DefaultKeyword
import com.github.javaparser.ast.Node
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers
import org.w3c.dom.Element

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
class AttribModifier : PseudoAttributeProvider {
    override fun attributeForNode(node: Node, owner: Element): Collection<JPAttrPseudo> {
        if (node is NodeWithModifiers<*>) {
            return DefaultKeyword.entries
                .map { JPAttrPseudo(it.name, { "" + node.hasModifier(it) }, owner) }
        }
        return listOf()
    }
}
