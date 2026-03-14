package io.github.jmltoolkit.xpath

import com.github.javaparser.ast.CompilationUnit
import org.w3c.dom.Document
import org.w3c.dom.NodeList
import java.io.StringWriter
import javax.xml.transform.OutputKeys
import javax.xml.transform.Source
import javax.xml.transform.TransformerException
import javax.xml.transform.TransformerFactory
import javax.xml.transform.dom.DOMSource
import javax.xml.transform.stream.StreamResult
import javax.xml.xpath.XPathConstants
import javax.xml.xpath.XPathExpressionException
import javax.xml.xpath.XPathFactory

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
object XPathFacade {
    @Throws(TransformerException::class)
    fun printXml(n: CompilationUnit): String {
        val xmlDocument: Document = DocumentFactories.getDocument(n)
        val transformerFactory = TransformerFactory.newInstance()
        val transformer = transformerFactory.newTransformer()
        transformer.setOutputProperty(OutputKeys.INDENT, "yes")
        val source: Source = DOMSource(xmlDocument.documentElement)
        val sw = StringWriter()
        val result = StreamResult(sw)
        transformer.transform(source, result)
        return sw.buffer.toString()
    }

    @Throws(XPathExpressionException::class)
    fun query(n: CompilationUnit, query: String?) {
        val xmlDocument: Document = DocumentFactories.getDocument(n)
        val xPath = XPathFactory.newInstance().newXPath()
        val res = xPath.compile(query).evaluate(xmlDocument, XPathConstants.NODESET) as NodeList
        for (i in 0 until res.length) {
            println((res.item(i) as JPElement).astNode)
        }
    }
}
