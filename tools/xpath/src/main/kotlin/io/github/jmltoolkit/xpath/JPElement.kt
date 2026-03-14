package io.github.jmltoolkit.xpath

import com.github.javaparser.ast.Node
import com.github.javaparser.ast.NodeList
import com.github.javaparser.metamodel.NodeMetaModel
import com.github.javaparser.metamodel.PropertyMetaModel
import org.w3c.dom.*

/**
 * @author Alexander Weigl
 * @version 1 (30.11.22)
 */
class JPElement(val astNode: Node, private val parent: Element) : Element {
    private val meta: NodeMetaModel = astNode.metaModel
    private var posInParent: Int = 0

    val children: List<JPElement> by lazy {
        meta.allPropertyMetaModels
            .filter(DocumentFactories::isNodeProperty)
            .map { it.getValue(this.astNode) }
            .flatMap {
                when (it) {
                    is NodeList<*> -> it.map { n -> DocumentFactories.getElement(n, this) }
                    is Node -> listOf(DocumentFactories.getElement(it, this))
                    else -> listOf()
                }
            }
            .map { it }
            .also {
                for (i in children.indices) {
                    children[i].posInParent = i
                }
            }
    }

    val attributes: List<Attr> by lazy {
        val attr = meta.allPropertyMetaModels
            .filter { !DocumentFactories.isNodeProperty(it) }
            .map { DocumentFactories.getAttribute(this, it) }
            .toMutableList()

        for (provider in DocumentFactories.attributeProviders) {
            val seq = provider.attributeForNode(astNode, this)
            attr.addAll(seq)
        }
        attr
    }

    override fun getTagName(): String = meta.typeName

    override fun getAttribute(name: String): String {
        val prop = getProperty(name)
        return prop.getValue(astNode).toString()
    }

    fun getProperty(name: String): PropertyMetaModel {
        return meta.allPropertyMetaModels.stream()
            .filter { it: PropertyMetaModel -> it.name == name }
            .findFirst().orElse(null)
    }

    @Throws(DOMException::class)
    override fun setAttribute(name: String, value: String) {
        throw IllegalStateException()
    }

    @Throws(DOMException::class)
    override fun removeAttribute(name: String) {
        throw IllegalStateException()
    }

    override fun getAttributeNode(name: String) = attributes.asSequence()
        .filter { it: Attr -> it.name == name }
        .firstOrNull()

    @Throws(DOMException::class)
    override fun setAttributeNode(newAttr: Attr): Attr? = null

    @Throws(DOMException::class)
    override fun removeAttributeNode(oldAttr: Attr): Attr? = null

    override fun getElementsByTagName(name: String): org.w3c.dom.NodeList {
        throw IllegalStateException()
    }

    @Throws(DOMException::class)
    override fun getAttributeNS(namespaceURI: String, localName: String): String {
        throw IllegalStateException()
    }

    @Throws(DOMException::class)
    override fun setAttributeNS(namespaceURI: String, qualifiedName: String, value: String) {
        throw IllegalStateException()
    }

    @Throws(DOMException::class)
    override fun removeAttributeNS(namespaceURI: String, localName: String) {
        throw IllegalStateException()
    }

    @Throws(DOMException::class)
    override fun getAttributeNodeNS(namespaceURI: String, localName: String): Attr {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
    }

    @Throws(DOMException::class)
    override fun setAttributeNodeNS(newAttr: Attr): Attr {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
    }

    @Throws(DOMException::class)
    override fun getElementsByTagNameNS(namespaceURI: String, localName: String): org.w3c.dom.NodeList {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
    }

    override fun hasAttribute(name: String): Boolean = !meta.allPropertyMetaModels.isEmpty()

    @Throws(DOMException::class)
    override fun hasAttributeNS(namespaceURI: String, localName: String): Boolean {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
    }

    override fun getSchemaTypeInfo(): TypeInfo? = null

    @Throws(DOMException::class)
    override fun setIdAttribute(name: String, isId: Boolean) {
    }

    @Throws(DOMException::class)
    override fun setIdAttributeNS(namespaceURI: String, localName: String, isId: Boolean) {
    }

    @Throws(DOMException::class)
    override fun setIdAttributeNode(idAttr: Attr, isId: Boolean) {
    }

    override fun getNodeName(): String = tagName

    @Throws(DOMException::class)
    override fun getNodeValue(): String = ""

    @Throws(DOMException::class)
    override fun setNodeValue(nodeValue: String) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
    }

    override fun getNodeType(): Short = org.w3c.dom.Node.ELEMENT_NODE

    override fun getParentNode(): org.w3c.dom.Node = parent

    override fun getChildNodes(): org.w3c.dom.NodeList = DocumentFactories.wrap(children)

    override fun getFirstChild() = children.firstOrNull()
    override fun getLastChild() = children.lastOrNull()

    override fun getPreviousSibling(): org.w3c.dom.Node? {
        if (posInParent != 0) {
            return parent.childNodes.item(posInParent - 1)
        }
        return null
    }

    override fun getNextSibling(): org.w3c.dom.Node? {
        if (posInParent + 1 < parent.childNodes.length) {
            return parent.childNodes.item(posInParent + 1)
        }
        return null
    }

    override fun getAttributes(): NamedNodeMap = DocumentFactories.nodeMap(this)

    override fun getOwnerDocument(): Document? = parent.ownerDocument

    @Throws(DOMException::class)
    override fun insertBefore(newChild: org.w3c.dom.Node, refChild: org.w3c.dom.Node): org.w3c.dom.Node {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
    }

    @Throws(DOMException::class)
    override fun replaceChild(newChild: org.w3c.dom.Node, oldChild: org.w3c.dom.Node): org.w3c.dom.Node {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
    }

    @Throws(DOMException::class)
    override fun removeChild(oldChild: org.w3c.dom.Node): org.w3c.dom.Node {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
    }

    @Throws(DOMException::class)
    override fun appendChild(newChild: org.w3c.dom.Node): org.w3c.dom.Node {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
    }

    override fun hasChildNodes(): Boolean = children.isNotEmpty()

    override fun cloneNode(deep: Boolean): org.w3c.dom.Node? = null

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
    override fun compareDocumentPosition(other: org.w3c.dom.Node): Short = 0

    @Throws(DOMException::class)
    override fun getTextContent(): String? = null

    @Throws(DOMException::class)
    override fun setTextContent(textContent: String) {
    }

    override fun isSameNode(other: org.w3c.dom.Node): Boolean = false

    override fun lookupPrefix(namespaceURI: String): String? = null

    override fun isDefaultNamespace(namespaceURI: String): Boolean = false

    override fun lookupNamespaceURI(prefix: String): String? = null

    override fun isEqualNode(arg: org.w3c.dom.Node): Boolean = false

    override fun getFeature(feature: String, version: String): Any? = null

    override fun setUserData(key: String, data: Any, handler: UserDataHandler): Any? = null

    override fun getUserData(key: String): Any? = null
}
