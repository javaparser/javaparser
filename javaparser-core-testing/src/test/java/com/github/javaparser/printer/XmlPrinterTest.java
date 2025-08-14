/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.printer;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static com.github.javaparser.StaticJavaParser.parseType;
import static org.junit.jupiter.api.Assertions.fail;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.type.Type;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.file.Files;
import java.util.HashSet;
import java.util.Set;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.XMLStreamWriter;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.w3c.dom.Document;
import org.xml.sax.SAXException;

class XmlPrinterTest {

    // Used for building XML documents
    private static DocumentBuilderFactory documentBuilderFactory;
    private static DocumentBuilder documentBuilder;

    @BeforeAll
    public static void setupDocumentBuilder() {
        try {
            documentBuilderFactory = DocumentBuilderFactory.newInstance();
            documentBuilderFactory.setNamespaceAware(true);
            documentBuilderFactory.setCoalescing(true);
            documentBuilderFactory.setIgnoringElementContentWhitespace(true);
            documentBuilderFactory.setIgnoringComments(true);
            documentBuilder = documentBuilderFactory.newDocumentBuilder();
        } catch (ParserConfigurationException ex) {
            throw new RuntimeException(ex);
        }
    }

    // Used for serializing XML documents (Necessary only when doing error reporting)
    private static TransformerFactory transformerFactory;
    private static Transformer transformer;

    @BeforeAll
    public static void setupTransformerFactory() {
        try {
            transformerFactory = TransformerFactory.newInstance();
            transformer = transformerFactory.newTransformer();
            transformer.setOutputProperty(OutputKeys.INDENT, "yes");
        } catch (TransformerConfigurationException ex) {
            throw new RuntimeException(ex);
        }
    }

    /**
     * Set of cleanups to be done at the end of each test execution.
     */
    private Set<Cleanup> cleanupSet;

    /**
     * Add given runnable to set of elements to be called.
     *
     * @param cleanup Object to be called at the end of each test execution
     */
    private void onEnd(Cleanup cleanup) {
        cleanupSet.add(cleanup);
    }

    @BeforeEach
    public void clearCleanupSet() {
        cleanupSet = new HashSet<>();
    }

    @AfterEach
    public void runCleanup() throws Exception {
        for (Cleanup cleanup : cleanupSet) {
            cleanup.run();
        }
    }

    public Document getDocument(String xml) throws SAXException, IOException {
        InputStream inputStream = new ByteArrayInputStream(xml.getBytes());
        Document result = documentBuilder.parse(inputStream);
        result.normalizeDocument();
        return result;
    }

    public String getXML(Document document) throws TransformerException {
        StringWriter result = new StringWriter(); // Closing a StringWriter is not needed
        transformer.transform(new DOMSource(document), new StreamResult(result));
        return result.toString();
    }

    private File createTempFile() throws IOException {
        File result = File.createTempFile("javaparser", "test.xml");
        onEnd(result::delete); // Schedule file deletion at the end of Test
        return result;
    }

    public void assertXMLEquals(String expected, String actual) throws SAXException, IOException {
        final Document expectedDocument = getDocument(expected);
        final Document actualDocument = getDocument(actual);

        if (!expectedDocument.isEqualNode(actualDocument)) {
            try {
                fail(String.format("-- expected:\n%s-- actual:\n%s", getXML(expectedDocument), getXML(actualDocument)));
            } catch (TransformerException ex) {
                fail(
                        String.format(
                                ""
                                        + "expected: <%s>, but it was <%s>\n"
                                        + "Additionally, a TransformerException was raised when trying to report XML document contents",
                                expected, actual),
                        ex);
            }
        }
    }

    @Test
    void testWithType() throws SAXException, IOException {
        Expression expression = parseExpression("1+1");
        XmlPrinter xmlOutput = new XmlPrinter(true);

        String output = xmlOutput.output(expression);

        assertXMLEquals(
                ""
                        // Expected
                        + "<root nodeType='BinaryExpr' operator='PLUS'>"
                        + "<left nodeType='IntegerLiteralExpr' value='1'></left>"
                        + "<right nodeType='IntegerLiteralExpr' value='1'></right>"
                        + "</root>",
                output);
    }

    @Test
    void testWithTypeXmlKeyCollision() throws SAXException, IOException {
        Type type = parseType("int");
        XmlPrinter xmlOutput = new XmlPrinter(true);

        String output = xmlOutput.output(type);

        assertXMLEquals("<root nodeType='PrimitiveType' type='INT'></root>", output);
    }

    @Test
    void testWithoutType() throws SAXException, IOException {
        Expression expression = parseExpression("1+1");

        XmlPrinter xmlOutput = new XmlPrinter(false);

        String output = xmlOutput.output(expression);

        assertXMLEquals("<root operator='PLUS'><left value='1'></left><right value='1'></right></root>", output);
    }

    @Test
    void testList() throws SAXException, IOException {
        Expression expression = parseExpression("a(1,2)");

        XmlPrinter xmlOutput = new XmlPrinter(true);

        String output = xmlOutput.output(expression);

        assertXMLEquals(
                ""
                        // Expected
                        + "<root nodeType='MethodCallExpr'>"
                        + "<name nodeType='SimpleName' identifier='a'></name>"
                        + "<arguments>"
                        + "<argument nodeType='IntegerLiteralExpr' value='1'></argument>"
                        + "<argument nodeType='IntegerLiteralExpr' value='2'></argument>"
                        + "</arguments>"
                        + "</root>",
                output);
    }

    // Demonstrate the use of streaming, without use of temporary strings.
    @Test
    void testStreamToFile() throws SAXException, IOException, XMLStreamException {

        File tempFile = createTempFile();

        try (FileWriter fileWriter = new FileWriter(tempFile)) {
            XmlPrinter xmlOutput = new XmlPrinter(false);
            xmlOutput.outputDocument(parseExpression("1+1"), "root", fileWriter);
        }

        assertXMLEquals(
                ""
                        // Expected
                        + "<root operator='PLUS'>"
                        + "<left value='1'/>"
                        + "<right value='1'/>"
                        + "</root>",
                // Actual (Using temporary string for checking results. No one has been used when generating XML)
                new String(Files.readAllBytes(tempFile.toPath())));
    }

    @Test
    void testCustomXML() throws SAXException, IOException, XMLStreamException {

        StringWriter stringWriter = new StringWriter();

        XMLOutputFactory outputFactory = XMLOutputFactory.newInstance();
        XMLStreamWriter xmlWriter = outputFactory.createXMLStreamWriter(stringWriter);
        onEnd(xmlWriter::close);

        XmlPrinter xmlOutput = new XmlPrinter(false);

        xmlWriter.writeStartDocument();
        xmlWriter.writeStartElement("custom");

        xmlOutput.outputNode(parseExpression("1+1"), "plusExpr", xmlWriter);
        xmlOutput.outputNode(parseExpression("a(1,2)"), "callExpr", xmlWriter);

        xmlWriter.writeEndElement();
        xmlWriter.writeEndDocument();
        xmlWriter.close();

        assertXMLEquals(
                ""
                        // Expected
                        + "<custom>"
                        + "<plusExpr operator='PLUS'>"
                        + "<left value='1'/>"
                        + "<right value='1'/>"
                        + "</plusExpr>"
                        + "<callExpr>"
                        + "<name identifier='a'/>"
                        + "<arguments>"
                        + "<argument value='1'/>"
                        + "<argument value='2'/>"
                        + "</arguments>"
                        + "</callExpr>"
                        + "</custom>",
                // Actual
                stringWriter.toString());
    }

    @Test
    void testAbsentTypeParameterList() throws SAXException, IOException, XMLStreamException {
        Expression expression = parseExpression("new HashSet()");
        XmlPrinter xmlOutput = new XmlPrinter(false);
        String output = xmlOutput.output(expression);
        assertXMLEquals(
                ""
                        // Expected
                        + "<root>"
                        + "<type>"
                        + "<name identifier='HashSet'/>"
                        + "</type>"
                        + "</root>",
                // Actual
                output);
    }

    @Test
    void testEmptyTypeParameterList() throws SAXException, IOException, XMLStreamException {
        Expression expression = parseExpression("new HashSet<>()");
        XmlPrinter xmlOutput = new XmlPrinter(false);
        String output = xmlOutput.output(expression);
        assertXMLEquals(
                ""
                        // Expected
                        + "<root>"
                        + "<type>"
                        + "<name identifier='HashSet'/>"
                        + "<typeArguments/>"
                        + "</type>"
                        + "</root>",
                // Actual
                output);
    }

    @Test
    void testNonEmptyTypeParameterList() throws SAXException, IOException, XMLStreamException {
        Expression expression = parseExpression("new HashSet<Integer,File>()");
        XmlPrinter xmlOutput = new XmlPrinter(false);
        String output = xmlOutput.output(expression);
        assertXMLEquals(
                ""
                        // Expected
                        + "<root>"
                        + "<type>"
                        + "<name identifier='HashSet'/>"
                        + "<typeArguments>"
                        + "<typeArgument>"
                        + "<name identifier='Integer'/>"
                        + "</typeArgument>"
                        + "<typeArgument>"
                        + "<name identifier='File'/>"
                        + "</typeArgument>"
                        + "</typeArguments>"
                        + "</type>"
                        + "</root>",
                // Actual
                output);
    }
}

interface Cleanup {
    void run() throws Exception;
}
