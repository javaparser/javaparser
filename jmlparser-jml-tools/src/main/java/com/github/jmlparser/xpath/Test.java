package com.github.jmlparser.xpath;

import com.github.javaparser.JavaParser;
import com.github.javaparser.StaticJavaParser;
import net.xqj.basex.local.BaseXXQDataSource;
import net.xqj.core.xqitemtype.XQItemTypeFactory;
import net.xqj.core.xqitemtype.XQItemTypeImpl;
import org.w3c.dom.Document;
import org.w3c.dom.NodeList;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;
import java.util.List;
import javax.xml.xquery.*;


/**
 * @author Alexander Weigl
 * @version 1 (30.11.22)
 */
public class Test {
    public static void main(String[] args) throws XPathExpressionException, TransformerException, XQException {
        var node = StaticJavaParser.parse("class A { public void foo(int x) { var a = 2;} } class B { public void foo(); }");
        /*
        JavaParser jp = new JavaParser();
        XPath path = new JavaParserXPath("ClassOrInterfaceDeclaration/@name", jp);
        List<?> results = path.selectNodes(node);
        System.out.println(results);
        path = new JavaParserXPath("string(ClassOrInterfaceDeclaration[1]/@name)", jp);
        results = path.selectNodes(node);
        System.out.println(results);
        */

        Document xmlDocument = DocumentFactories.getDocument(node);

        TransformerFactory transformerFactory = TransformerFactory.newInstance();
        Transformer transformer = transformerFactory.newTransformer();
        transformer.setOutputProperty(OutputKeys.INDENT, "yes");
        Source source = new DOMSource(xmlDocument.getDocumentElement());
        StreamResult result = new StreamResult(System.out);
        transformer.transform(source, result);

        XPath xPath = XPathFactory.newInstance().newXPath();
        String expression = "//*[@name]";
        var res = (NodeList) xPath.compile(expression).evaluate(xmlDocument, XPathConstants.NODESET);
        for (int i = 0; i < res.getLength(); i++) {
            System.out.println(((JPElement) res.item(i)).getAstNode());
        }
    }
}
