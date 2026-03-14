package io.github.jmltoolkit.xpath

import com.github.javaparser.ast.CompilationUnit
import com.github.javaparser.ast.Node
import com.github.javaparser.metamodel.PropertyMetaModel
import org.w3c.dom.*
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (30.11.22)
 */
object DocumentFactories {
    val attributeProviders by lazy {
        ServiceLoader.load(PseudoAttributeProvider::class.java).toList()
    }

    fun isNodeProperty(mm: PropertyMetaModel): Boolean = mm.isNode || mm.isNodeList

    fun getDocument(node: CompilationUnit): Document = JPDocument(node)

    fun getElement(it: Node, parent: Element): JPElement = JPElement(it, parent)


    fun <T : org.w3c.dom.Node> wrap(list: List<T>): NodeList {
        return object : NodeList {
            override fun item(index: Int): org.w3c.dom.Node = list[index]

            override fun getLength(): Int = list.size
        }
    }

    fun wrap(vararg seq: Element): NodeList = wrap(listOf(*seq))

    fun emptyNodeMap(): NamedNodeMap {
        return object : NamedNodeMap {
            override fun getNamedItem(name: String): org.w3c.dom.Node? = null

            @Throws(DOMException::class)
            override fun setNamedItem(arg: org.w3c.dom.Node): org.w3c.dom.Node? = null

            @Throws(DOMException::class)
            override fun removeNamedItem(name: String): org.w3c.dom.Node? = null

            override fun item(index: Int): org.w3c.dom.Node? = null

            override fun getLength(): Int = 0

            @Throws(DOMException::class)
            override fun getNamedItemNS(namespaceURI: String, localName: String): org.w3c.dom.Node? = null

            @Throws(DOMException::class)
            override fun setNamedItemNS(arg: org.w3c.dom.Node): org.w3c.dom.Node? = null

            @Throws(DOMException::class)
            override fun removeNamedItemNS(namespaceURI: String, localName: String): org.w3c.dom.Node? = null
        }
    }

    fun getAttribute(jpElement: JPElement, it: PropertyMetaModel): Attr = JPAttr(jpElement, it)

    fun nodeMap(jpElement: JPElement): NamedNodeMap {
        return object : NamedNodeMap {
            override fun getNamedItem(name: String) =
                jpElement.attributes.firstOrNull { it.name.equals(name) }

            @Throws(DOMException::class)
            override fun setNamedItem(arg: org.w3c.dom.Node): org.w3c.dom.Node {
                throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
            }

            @Throws(DOMException::class)
            override fun removeNamedItem(name: String): org.w3c.dom.Node {
                throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
            }

            override fun item(index: Int): org.w3c.dom.Node = jpElement.attributes[index]

            override fun getLength(): Int = jpElement.attributes.size

            @Throws(DOMException::class)
            override fun getNamedItemNS(namespaceURI: String, localName: String): org.w3c.dom.Node {
                throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
            }

            @Throws(DOMException::class)
            override fun setNamedItemNS(arg: org.w3c.dom.Node): org.w3c.dom.Node {
                throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
            }

            @Throws(DOMException::class)
            override fun removeNamedItemNS(namespaceURI: String, localName: String): org.w3c.dom.Node {
                throw DOMException(DOMException.NOT_SUPPORTED_ERR, "")
            }
        }
    }
}
