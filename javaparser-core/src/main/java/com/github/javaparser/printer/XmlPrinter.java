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
import java.util.function.Predicate;

/**
 * Outputs an XML file containing the AST meant for inspecting it.
 */
public class XmlPrinter {

    private final boolean outputNodeType;

    public XmlPrinter(boolean outputNodeType) {
        this.outputNodeType = outputNodeType;
    }

    public String output(Node node) {
        StringBuilder output = new StringBuilder();
        output(node, "root", 0, output);
        return output.toString();
    }

    public void output(Node node, String name, int level, StringBuilder builder) {
        assertNotNull(node);
        NodeMetaModel metaModel = node.getMetaModel();
        List<PropertyMetaModel> allPropertyMetaModels = metaModel.getAllPropertyMetaModels();
        Predicate<PropertyMetaModel> nonNullNode = propertyMetaModel -> propertyMetaModel.getValue(node) != null;
        Predicate<PropertyMetaModel> nonEmptyList = propertyMetaModel ->
                ((NodeList) propertyMetaModel.getValue(node)).isNonEmpty();

        builder.append("<").append(name);

        // Output node type attribute
        if (outputNodeType) {
            builder.append(attribute("type", metaModel.getTypeName()));
        }

        // Output attributes
        allPropertyMetaModels.stream()
                .filter(PropertyMetaModel::isAttribute)
                .filter(PropertyMetaModel::isSingular)
                .forEach(attributeMetaModel -> {
                        final String attributeName = attributeMetaModel.getName();
                        final String attributeValue = attributeMetaModel.getValue(node).toString();
                        builder.append(attribute(attributeName, attributeValue));
                });

        builder.append(">");

        // Output singular subNodes
        allPropertyMetaModels.stream()
                .filter(PropertyMetaModel::isNode)
                .filter(PropertyMetaModel::isSingular)
                .filter(nonNullNode)
                .forEach(subNodeMetaModel -> {
                        final Node subNode = (Node) subNodeMetaModel.getValue(node);
                        final String subNodeName = subNodeMetaModel.getName();
                        output(subNode, subNodeName, level + 1, builder);
                });

        // Output list subNodes
        allPropertyMetaModels.stream()
                .filter(PropertyMetaModel::isNodeList)
                .filter(nonNullNode)
                .filter(nonEmptyList)
                .forEach(listMetaModel -> {
                        final String listName = listMetaModel.getName();
                        String singular = listName.substring(0, listName.length() - 1);
                        NodeList<? extends Node> nodeList = (NodeList) listMetaModel.getValue(node);
                        builder.append("<").append(listName).append(">");
                        for (Node subNode : nodeList) {
                            output(subNode, singular, level + 1, builder);
                        }
                        builder.append(close(listName));
                });
        builder.append(close(name));
    }

    private static String close(String name) {
        return "</" + name + ">";
    }

    private static String attribute(String name, String value) {
        return " " + name + "='" + value + "'";
    }

    public static void print(Node node) {
        System.out.println(new XmlPrinter(true).output(node));
    }
}
