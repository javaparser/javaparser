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

import static com.github.javaparser.utils.Utils.assertNonEmpty;
import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.metamodel.NodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import java.io.StringWriter;
import java.io.Writer;
import java.util.List;
import java.util.function.Predicate;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.XMLStreamWriter;

/**
 * Outputs an XML file containing the AST meant for inspecting it.
 */
public class XmlPrinter {

    private final boolean outputNodeType;

    private static final Class<?> TYPE_CLASS = Type.class;

    public XmlPrinter(boolean outputNodeType) {
        this.outputNodeType = outputNodeType;
    }

    /**
     * Generate a xml string for given AST Node. Tag name of root element in the result document will be "root".
     *
     * @param node AST node to be converted to XML
     * @return XML document corresponding to node
     */
    public String output(Node node) {
        return stringWriterOutput(node, "root").toString();
    }

    /**
     * Output XML data from an AST node to a String Builder. This method is kept for backward compatilibity only and
     * should be removed in future releases.
     *
     * @param node AST node to be converted to XML
     * @param name Tag name of root element in the resulting document
     * @param level Nesting level of node in tree. Not used.
     * @param builder Target object to receive the generated XML
     */
    @Deprecated
    public void output(Node node, String name, int level, StringBuilder builder) {
        builder.append(stringWriterOutput(node, name).toString());
    }

    /**
     * Create a string writer filled with XML document representing an AST node.
     * <p>
     * Returned stringWriter is not closed upon return because doing so {@link StringWriter#close() has no effect}.
     * So users of this method are not required to close it.
     * </p>
     * @param node AST node to be converted to XML
     * @param name Tag name of root element in the resulting document
     * @return Stringwriter filled with XML document
     * @throws RuntimeXMLStreamException Unchecked exception wrapping checked {@link XMLStreamException}, when any
     * error on producing XML output occours
     */
    public StringWriter stringWriterOutput(Node node, String name) {
        StringWriter stringWriter = new StringWriter();
        try {
            outputDocument(node, name, stringWriter);
        } catch (XMLStreamException ex) {
            throw new RuntimeXMLStreamException(ex);
        }
        return stringWriter;
    }

    /**
     * Output the XML Document representing given AST node to given writer.
     * <p>
     * This method creates a {@link XMLStreamWriter} that writes to given writer and delegates execution to
     * {@link #outputDocument(Node, String, XMLStreamWriter)}
     * </p>
     * <p>
     * Provided writer is NOT closed at the end of execution of this method.
     * </p>
     *
     * @param node AST node to be converted to XML
     * @param name Tag name of root element of document
     * @param writer Target to get the document writen to
     * @throws XMLStreamException When any error on outputting XML occours
     */
    public void outputDocument(Node node, String name, Writer writer) throws XMLStreamException {
        XMLOutputFactory outputFactory = XMLOutputFactory.newInstance();
        XMLStreamWriter xmlWriter = outputFactory.createXMLStreamWriter(writer);
        try {
            outputDocument(node, name, xmlWriter);
        } finally {
            xmlWriter.close();
        }
    }

    /**
     * Output the XML Document representing an AST node to given XMLStreamWriter.
     * <p>
     * This method outputs the starting of XML document, then delegates to
     * {@link #outputNode(Node, String, XMLStreamWriter) for writing the root element of XML document, and finally
     * outputs the ending of XML document.
     * </p>
     * <p>
     * This method is used when the root element of an XML document corresponds to an AST node. Would an element
     * corresponding to an AST node be written as child of another element, then
     * {@link #outputNode(String, Node, XMLStreamWriter)} should be used instead. Actually, outputNode is used
     * recursively for outputting nested elements from AST.
     * </p>
     * <p>
     * Provided xmlWriter is NOT closed at the end of execution of this method.
     * </p>
     *
     * @param node AST node to be converted to XML
     * @param name Tag name of root element of document
     * @param xmlWriter Target to get document written to
     * @throws XMLStreamException When any error on outputting XML occours
     * @see outputNode(String, Node, XMLStreamWriter)
     */
    public void outputDocument(Node node, String name, XMLStreamWriter xmlWriter) throws XMLStreamException {
        xmlWriter.writeStartDocument();
        outputNode(node, name, xmlWriter);
        xmlWriter.writeEndDocument();
    }

    /**
     * Output the XML Element representing an AST node to given writer.
     * <p>
     * This method outputs an XML Element with given tag name to writer. It is used recursively for generating nested
     * elements corresponding to AST.
     * </p>
     * <p>
     * For generating a complete XML document from an AST node, {@link outputDocument(String, Node, XMLStreamWriter)}
     * should be used instead.
     * </p>
     * <p>
     * Provided xmlWriter is NOT closed at the end of execution of this method.
     * </p>
     *
     * @param node AST node to be converted to XML
     * @param name Tag name of element corresponding to node
     * @param xmlWriter Target to get XML written to
     * @throws XMLStreamException When any error on outputting XML occours
     * @see outputDocument(String, Node, XMLStreamWriter)
     */
    public void outputNode(Node node, String name, XMLStreamWriter xmlWriter) throws XMLStreamException {
        assertNotNull(node);
        assertNonEmpty(name);
        assertNotNull(xmlWriter);
        NodeMetaModel metaModel = node.getMetaModel();
        List<PropertyMetaModel> allPropertyMetaModels = metaModel.getAllPropertyMetaModels();
        Predicate<PropertyMetaModel> nonNullNode = propertyMetaModel -> propertyMetaModel.getValue(node) != null;
        Predicate<PropertyMetaModel> nonEmptyList =
                propertyMetaModel -> ((NodeList) propertyMetaModel.getValue(node)).isNonEmpty();
        Predicate<PropertyMetaModel> typeList = propertyMetaModel -> TYPE_CLASS == propertyMetaModel.getType();
        xmlWriter.writeStartElement(name);
        // Output node type attribute
        if (outputNodeType) {
            xmlWriter.writeAttribute("nodeType", metaModel.getTypeName());
        }
        try {
            // Output attributes
            allPropertyMetaModels.stream()
                    .filter(PropertyMetaModel::isAttribute)
                    .filter(PropertyMetaModel::isSingular)
                    .forEach(attributeMetaModel -> {
                        try {
                            final String attributeName = attributeMetaModel.getName();
                            final String attributeValue =
                                    attributeMetaModel.getValue(node).toString();
                            xmlWriter.writeAttribute(attributeName, attributeValue);
                        } catch (XMLStreamException ex) {
                            throw new RuntimeXMLStreamException(ex);
                        }
                    });
            // Output singular subNodes
            allPropertyMetaModels.stream()
                    .filter(PropertyMetaModel::isNode)
                    .filter(PropertyMetaModel::isSingular)
                    .filter(nonNullNode)
                    .forEach(subNodeMetaModel -> {
                        try {
                            final Node subNode = (Node) subNodeMetaModel.getValue(node);
                            final String subNodeName = subNodeMetaModel.getName();
                            outputNode(subNode, subNodeName, xmlWriter);
                        } catch (XMLStreamException ex) {
                            throw new RuntimeXMLStreamException(ex);
                        }
                    });
            // Output list subNodes
            allPropertyMetaModels.stream()
                    .filter(PropertyMetaModel::isNodeList)
                    .filter(nonNullNode)
                    .filter(nonEmptyList.or(typeList))
                    .forEach(listMetaModel -> {
                        try {
                            String listName = listMetaModel.getName();
                            String singular = listName.substring(0, listName.length() - 1);
                            NodeList<? extends Node> nodeList = (NodeList) listMetaModel.getValue(node);
                            xmlWriter.writeStartElement(listName);
                            for (Node subNode : nodeList) {
                                outputNode(subNode, singular, xmlWriter);
                            }
                            xmlWriter.writeEndElement();
                        } catch (XMLStreamException ex) {
                            throw new RuntimeXMLStreamException(ex);
                        }
                    });
        } catch (RuntimeXMLStreamException ex) {
            throw ex.getXMLStreamCause();
        }
        xmlWriter.writeEndElement();
    }

    public static void print(Node node) {
        System.out.println(new XmlPrinter(true).output(node));
    }
}

/**
 * RuntimeException subclass encapsulationg XMLStreamException.
 * <p>
 * Used for generating methods without checked exceptions, but allowing to selectively capture of XMLStreamException at
 * higher levels.
 * </p>
 */
class RuntimeXMLStreamException extends RuntimeException {

    public RuntimeXMLStreamException(XMLStreamException cause) {
        super(cause);
    }

    public XMLStreamException getXMLStreamCause() {
        return (XMLStreamException) super.getCause();
    }
}
