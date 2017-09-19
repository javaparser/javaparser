package com.github.javaparser.printer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.metamodel.NodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import java.util.List;

import static com.github.javaparser.utils.Utils.assertNotNull;
import static java.util.stream.Collectors.toList;

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
        List<PropertyMetaModel> attributes = allPropertyMetaModels.stream().filter(PropertyMetaModel::isAttribute).filter(PropertyMetaModel::isSingular).collect(toList());
        List<PropertyMetaModel> subNodes = allPropertyMetaModels.stream().filter(PropertyMetaModel::isNode).filter(PropertyMetaModel::isSingular).collect(toList());
        List<PropertyMetaModel> subLists = allPropertyMetaModels.stream().filter(PropertyMetaModel::isNodeList).collect(toList());

        builder.append("<").append(name);
        if (outputNodeType) {
            builder.append(attribute("type", metaModel.getTypeName()));
        }

        for (PropertyMetaModel attributeMetaModel : attributes) {
            builder.append(attribute(attributeMetaModel.getName(), attributeMetaModel.getValue(node).toString()));
        }
        builder.append(">");

        for (PropertyMetaModel subNodeMetaModel : subNodes) {
            Node value = (Node) subNodeMetaModel.getValue(node);
            if (value != null) {
                output(value, subNodeMetaModel.getName(), level + 1, builder);
            }
        }

        for (PropertyMetaModel subListMetaModel : subLists) {
            NodeList<? extends Node> subList = (NodeList<? extends Node>) subListMetaModel.getValue(node);
            if (subList != null && !subList.isEmpty()) {
                String listName = subListMetaModel.getName();
                builder.append("<").append(listName).append(">");
                String singular = listName.substring(0, listName.length() - 1);
                for (Node subListNode : subList) {
                    output(subListNode, singular, level + 1, builder);
                }
                builder.append(close(listName));
            }
        }
        builder.append(close(name));
    }

    private static String close(String name) {
        return "</" + name + ">";
    }

    private static String attribute(String name, String value) {
        return " " + name + "='" + value + "'";
    }
}

