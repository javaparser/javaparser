package io.github.jmltoolkit.xpath

import com.github.javaparser.ast.Node
import org.w3c.dom.Element

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
abstract class PseudoAttributeHelper<T : Node?> protected constructor(private val clazz: Class<T>) :
    PseudoAttributeProvider {
    @Suppress("UNCHECKED_CAST")
    override fun attributeForNode(node: Node, owner: Element): Collection<JPAttrPseudo> {
        if (clazz == node.javaClass) {
            return attributes(node as T, owner)
        }
        return listOf()
    }

    protected abstract fun attributes(node: T, owner: Element?): Collection<JPAttrPseudo>
}
