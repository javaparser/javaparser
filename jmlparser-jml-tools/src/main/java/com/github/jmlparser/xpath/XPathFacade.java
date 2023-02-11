package com.github.jmlparser.xpath;

import com.github.javaparser.ast.CompilationUnit;
import org.w3c.dom.Document;
import org.w3c.dom.NodeList;

import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;
import java.io.StringWriter;

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
public class XPathFacade {
    public static String printXml(CompilationUnit n) throws TransformerException {
        Document xmlDocument = DocumentFactories.getDocument(n);
        TransformerFactory transformerFactory = TransformerFactory.newInstance();
        Transformer transformer = transformerFactory.newTransformer();
        transformer.setOutputProperty(OutputKeys.INDENT, "yes");
        Source source = new DOMSource(xmlDocument.getDocumentElement());
        var sw = new StringWriter();
        StreamResult result = new StreamResult(sw);
        transformer.transform(source, result);
        return sw.getBuffer().toString();
    }

    public static void query(CompilationUnit n, String query) throws XPathExpressionException {
        Document xmlDocument = DocumentFactories.getDocument(n);
        XPath xPath = XPathFactory.newInstance().newXPath();
        var res = (NodeList) xPath.compile(query).evaluate(xmlDocument, XPathConstants.NODESET);
        for (int i = 0; i < res.getLength(); i++) {
            System.out.println(((JPElement) res.item(i)).getAstNode());
        }
    }
}
