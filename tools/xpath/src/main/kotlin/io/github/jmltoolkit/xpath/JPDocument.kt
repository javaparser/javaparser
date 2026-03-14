package io.github.jmltoolkit.xpath

import com.github.javaparser.ast.CompilationUnit
import org.w3c.dom.*

class JPDocument(node: CompilationUnit) : Document {
    private val root: JPRootElement = JPRootElement(listOf(node), this)

    override fun getDoctype(): DocumentType? = null

    override fun getImplementation(): DOMImplementation? = null

    override fun getDocumentElement(): Element = root

    @Throws(DOMException::class)
    override fun createElement(tagName: String): Element {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun createDocumentFragment(): DocumentFragment? = null

    override fun createTextNode(data: String): Text? = null

    override fun createComment(data: String): Comment? = null

    @Throws(DOMException::class)
    override fun createCDATASection(data: String): CDATASection {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun createProcessingInstruction(target: String, data: String): ProcessingInstruction {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun createAttribute(name: String): Attr {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun createEntityReference(name: String): EntityReference {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getElementsByTagName(tagname: String): NodeList {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun importNode(importedNode: Node, deep: Boolean): Node {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun createElementNS(namespaceURI: String, qualifiedName: String): Element {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun createAttributeNS(namespaceURI: String, qualifiedName: String): Attr {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getElementsByTagNameNS(namespaceURI: String, localName: String): NodeList {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getElementById(elementId: String): Element? = null

    override fun getInputEncoding(): String = "utf-8"

    override fun getXmlEncoding(): String = "utf-8"

    override fun getXmlStandalone(): Boolean = true

    @Throws(DOMException::class)
    override fun setXmlStandalone(xmlStandalone: Boolean) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getXmlVersion(): String = "1.0"

    @Throws(DOMException::class)
    override fun setXmlVersion(xmlVersion: String) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getStrictErrorChecking(): Boolean = false

    override fun setStrictErrorChecking(strictErrorChecking: Boolean) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getDocumentURI(): String? = null

    override fun setDocumentURI(documentURI: String) {
    }

    @Throws(DOMException::class)
    override fun adoptNode(source: Node): Node? = null

    override fun getDomConfig(): DOMConfiguration? = null

    override fun normalizeDocument() {
    }

    @Throws(DOMException::class)
    override fun renameNode(n: Node, namespaceURI: String, qualifiedName: String): Node {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getNodeName(): String = "#document"

    @Throws(DOMException::class)
    override fun getNodeValue(): String {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun setNodeValue(nodeValue: String) {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    override fun getNodeType(): Short = Node.DOCUMENT_TYPE_NODE

    override fun getParentNode(): Node? = null

    override fun getChildNodes(): NodeList = DocumentFactories.wrap(root)

    override fun getFirstChild(): Node = root

    override fun getLastChild(): Node = root

    override fun getPreviousSibling(): Node? = null

    override fun getNextSibling(): Node? = null

    override fun getAttributes(): NamedNodeMap? = null

    override fun getOwnerDocument(): Document = this

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

    override fun hasChildNodes(): Boolean = root != null

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
    override fun compareDocumentPosition(other: Node): Short {
        throw DOMException(DOMException.NOT_SUPPORTED_ERR, "Not Supported")
    }

    @Throws(DOMException::class)
    override fun getTextContent(): String? = null

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
