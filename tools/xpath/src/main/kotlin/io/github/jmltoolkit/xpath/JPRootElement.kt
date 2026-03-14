package io.github.jmltoolkit.xpath

import com.github.javaparser.ast.CompilationUnit
import org.w3c.dom.*


class JPRootElement(private val nodes: List<CompilationUnit>, private val document: JPDocument) : Element {
    private val elements: List<Element> by lazy {
        nodes.map { DocumentFactories.getElement(it, this) }
    }

    override fun getTagName(): String = "project"

    override fun getAttribute(name: String): String = ""

    @Throws(DOMException::class)
    override fun setAttribute(name: String, value: String) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun removeAttribute(name: String) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getAttributeNode(name: String): Attr? = null

    @Throws(DOMException::class)
    override fun setAttributeNode(newAttr: Attr): Attr {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun removeAttributeNode(oldAttr: Attr): Attr {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getElementsByTagName(name: String): NodeList {
        throw IllegalStateException()
    }

    @Throws(DOMException::class)
    override fun getAttributeNS(namespaceURI: String, localName: String): String = ""

    @Throws(DOMException::class)
    override fun setAttributeNS(namespaceURI: String, qualifiedName: String, value: String) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun removeAttributeNS(namespaceURI: String, localName: String) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun getAttributeNodeNS(namespaceURI: String, localName: String): Attr? = null

    @Throws(DOMException::class)
    override fun setAttributeNodeNS(newAttr: Attr): Attr {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun getElementsByTagNameNS(namespaceURI: String, localName: String): NodeList {
        throw IllegalStateException()
    }

    override fun hasAttribute(name: String): Boolean = false

    @Throws(DOMException::class)
    override fun hasAttributeNS(namespaceURI: String, localName: String): Boolean = false

    override fun getSchemaTypeInfo(): TypeInfo? = null

    @Throws(DOMException::class)
    override fun setIdAttribute(name: String, isId: Boolean) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun setIdAttributeNS(namespaceURI: String, localName: String, isId: Boolean) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun setIdAttributeNode(idAttr: Attr, isId: Boolean) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getNodeName(): String = tagName

    @Throws(DOMException::class)
    override fun getNodeValue(): String {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun setNodeValue(nodeValue: String) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getNodeType(): Short = Node.ELEMENT_NODE

    override fun getParentNode(): Node = document

    override fun getChildNodes(): NodeList = DocumentFactories.wrap(elements)

    override fun getFirstChild(): Node = elements.first()

    override fun getLastChild(): Node = elements.last()

    override fun getPreviousSibling(): Node? = null

    override fun getNextSibling(): Node? = null

    override fun getAttributes(): NamedNodeMap = DocumentFactories.emptyNodeMap()

    override fun getOwnerDocument(): Document = document

    @Throws(DOMException::class)
    override fun insertBefore(newChild: Node, refChild: Node): Node {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun replaceChild(newChild: Node, oldChild: Node): Node {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun removeChild(oldChild: Node): Node {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun appendChild(newChild: Node): Node {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun hasChildNodes(): Boolean = elements.isNotEmpty()

    override fun cloneNode(deep: Boolean): Node? = null

    override fun normalize() {
    }

    override fun isSupported(feature: String, version: String): Boolean = false

    override fun getNamespaceURI(): String? = null

    override fun getPrefix(): String? = null

    @Throws(DOMException::class)
    override fun setPrefix(prefix: String) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getLocalName(): String? = null

    override fun hasAttributes(): Boolean = false

    override fun getBaseURI(): String? = null

    @Throws(DOMException::class)
    override fun compareDocumentPosition(other: Node): Short = 0

    @Throws(DOMException::class)
    override fun getTextContent(): String = ""

    @Throws(DOMException::class)
    override fun setTextContent(textContent: String) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun isSameNode(other: Node): Boolean {
        return other is JPRootElement &&
                this.document === other.document
    }

    override fun lookupPrefix(namespaceURI: String): String = ""

    override fun isDefaultNamespace(namespaceURI: String): Boolean = false

    override fun lookupNamespaceURI(prefix: String): String? = null

    override fun isEqualNode(arg: Node): Boolean = false

    override fun getFeature(feature: String, version: String): Any? = null

    override fun setUserData(key: String, data: Any, handler: UserDataHandler): Any? = null

    override fun getUserData(key: String): Any? = null
}