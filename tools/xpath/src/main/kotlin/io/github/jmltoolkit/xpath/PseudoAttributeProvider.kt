package io.github.jmltoolkit.xpath

import com.github.javaparser.ast.Node
import org.w3c.dom.Element

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
interface PseudoAttributeProvider {
    fun attributeForNode(node: Node, owner: Element): Collection<JPAttrPseudo>
}
