/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.metamodel.NodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import java.util.List;

import static com.github.javaparser.utils.Utils.assertNotNull;
import java.io.StringWriter;
import java.io.Writer;
import java.util.function.Predicate;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.XMLStreamWriter;

/**
 * Outputs an XML file containing the AST meant for inspecting it.
 */
public class XmlPrinter {

    private final boolean outputNodeType;

    public XmlPrinter(boolean outputNodeType) {
        this.outputNodeType = outputNodeType;
    }

    public String output(Node node) {
        return stringWriterOutput(node, "root").toString();
    }

    // Kept for backward compatibility
    public void output(Node node, String name, int level, StringBuilder builder) {
        builder.append(stringWriterOutput(node, name).toString());
    }

    public StringWriter stringWriterOutput(Node node, String name) {
        StringWriter stringWriter = new StringWriter();
        outputDocument(node, name, stringWriter);
        return stringWriter;
    }

    public void outputDocument(Node node, String name, Writer writer) {
        XMLOutputFactory outputFactory = XMLOutputFactory.newInstance();
        try {
            XMLStreamWriter xmlWriter = outputFactory.createXMLStreamWriter(writer);
            outputDocument(node, name, xmlWriter);
        } catch (XMLStreamException ex) {
            throw new RuntimeXMLStreamException(ex);
        }
    }

    public void outputDocument(Node node, String name, XMLStreamWriter xmlWriter) throws XMLStreamException {
        xmlWriter.writeStartDocument();
        outputNode(node, name, xmlWriter);
        xmlWriter.writeEndDocument();
    }

    public void outputNode(Node node, String name, XMLStreamWriter xmlWriter) throws XMLStreamException {

        assertNotNull(node);
        NodeMetaModel metaModel = node.getMetaModel();
        List<PropertyMetaModel> allPropertyMetaModels = metaModel.getAllPropertyMetaModels();
        Predicate<PropertyMetaModel> nonNullNode = propertyMetaModel -> propertyMetaModel.getValue(node) != null;
        Predicate<PropertyMetaModel> nonEmptyList = propertyMetaModel ->
                ((NodeList) propertyMetaModel.getValue(node)).isNonEmpty();

        xmlWriter.writeStartElement(name);

        // Output node type attribute
        if (outputNodeType) {
            xmlWriter.writeAttribute("type", metaModel.getTypeName());
        }

        try {
            // Output attributes
            allPropertyMetaModels.stream()
                    .filter(PropertyMetaModel::isAttribute)
                    .filter(PropertyMetaModel::isSingular)
                    .forEach(attributeMetaModel -> {
                        try {
                            final String attributeName = attributeMetaModel.getName();
                            final String attributeValue = attributeMetaModel.getValue(node).toString();
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
                    .filter(nonEmptyList)
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

class RuntimeXMLStreamException extends RuntimeException {

    public RuntimeXMLStreamException(XMLStreamException cause) {
        super(cause);
    }

    public XMLStreamException getXMLStreamCause() {
        return (XMLStreamException) super.getCause();
    }
}
