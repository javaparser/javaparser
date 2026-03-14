package io.github.jmltoolkit.xpath

import com.github.javaparser.ast.Node
import com.github.javaparser.ast.nodeTypes.NodeWithName
import org.w3c.dom.Element

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
class AttribNodeWithName : PseudoAttributeProvider {
    override fun attributeForNode(node: Node, owner: Element): Collection<JPAttrPseudo> {
        if (node is NodeWithName<*>) {
            return setOf(JPAttrPseudo("name", { node.nameAsString }, owner))
        }
        return listOf()
    }
}
