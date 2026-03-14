package io.github.jmltoolkit.xpath

import org.w3c.dom.*
import java.util.function.Supplier

/**
 * @author Alexander Weigl
 * @version 1 (01.12.22)
 */
class JPAttrPseudo(private val _name: String, private val supplier: Supplier<String>, private val owner: Element) : Attr {
    override fun getName(): String = _name

    override fun getSpecified(): Boolean = true

    override fun getValue(): String = supplier.get()

    @Throws(DOMException::class)
    override fun setValue(value: String) {
        throw IllegalStateException()
    }

    override fun getOwnerElement(): Element = owner

    override fun getSchemaTypeInfo(): TypeInfo? = null

    override fun isId(): Boolean = false

    override fun getNodeName(): String = getName()

    @Throws(DOMException::class)
    override fun getNodeValue(): String = value

    @Throws(DOMException::class)
    override fun setNodeValue(nodeValue: String) {
        throw RuntimeException()
    }

    override fun getNodeType(): Short = Node.ATTRIBUTE_NODE

    override fun getParentNode(): Node = ownerElement

    override fun getChildNodes(): NodeList = DocumentFactories.wrap()

    override fun getFirstChild(): Node? = null

    override fun getLastChild(): Node? = null

    override fun getPreviousSibling(): Node? = null

    override fun getNextSibling(): Node? = null

    override fun getAttributes(): NamedNodeMap? = null

    override fun getOwnerDocument(): Document = parentNode.ownerDocument

    @Throws(DOMException::class)
    override fun insertBefore(newChild: Node, refChild: Node): Node? = null

    @Throws(DOMException::class)
    override fun replaceChild(newChild: Node, oldChild: Node): Node? = null

    @Throws(DOMException::class)
    override fun removeChild(oldChild: Node): Node? = null

    @Throws(DOMException::class)
    override fun appendChild(newChild: Node): Node? = null

    override fun hasChildNodes(): Boolean = false

    override fun cloneNode(deep: Boolean): Node? = null

    override fun normalize() {
    }

    override fun isSupported(feature: String, version: String): Boolean = false

    override fun getNamespaceURI(): String? = null

    override fun getPrefix(): String? = null

    @Throws(DOMException::class)
    override fun setPrefix(prefix: String) {
    }

    override fun getLocalName(): String? = null

    override fun hasAttributes(): Boolean = false

    override fun getBaseURI(): String? = null

    @Throws(DOMException::class)
    override fun compareDocumentPosition(other: Node): Short = 0

    @Throws(DOMException::class)
    override fun getTextContent(): String = value

    @Throws(DOMException::class)
    override fun setTextContent(textContent: String) {
    }

    override fun isSameNode(other: Node): Boolean = false

    override fun lookupPrefix(namespaceURI: String): String? = null

    override fun isDefaultNamespace(namespaceURI: String): Boolean = false

    override fun lookupNamespaceURI(prefix: String): String? = null

    override fun isEqualNode(arg: Node): Boolean = false

    override fun getFeature(feature: String, version: String): Any? = null

    override fun setUserData(key: String, data: Any, handler: UserDataHandler): Any? = null

    override fun getUserData(key: String): Any? = null
}
