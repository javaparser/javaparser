package com.github.javaparser.ast.visitor.treestructure;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.metamodel.NodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SeparatedItemStringBuilder;

import java.util.List;

import static com.github.javaparser.metamodel.Multiplicity.ONE;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static java.util.stream.Collectors.toList;

public class JsonDump {
    private final boolean outputNodeType;

    public JsonDump(boolean outputNodeType) {
        this.outputNodeType = outputNodeType;
    }

    public String output(Node node) {
        return output(node, null, 0);
    }

    public String output(Node node, String name, int level) {
        assertNotNull(node);
        NodeMetaModel metaModel = node.getMetaModel();
        List<PropertyMetaModel> allPropertyMetaModels = metaModel.getAllPropertyMetaModels();
        List<PropertyMetaModel> attributes = allPropertyMetaModels.stream().filter(PropertyMetaModel::isAttribute).filter(p -> p.getMultiplicity() == ONE).collect(toList());
        List<PropertyMetaModel> subNodes = allPropertyMetaModels.stream().filter(PropertyMetaModel::isNode).filter(p -> p.getMultiplicity() == ONE).collect(toList());
        List<PropertyMetaModel> subLists = allPropertyMetaModels.stream().filter(PropertyMetaModel::isNodeList).collect(toList());

        final SeparatedItemStringBuilder content;
        if (name == null) {
            content = new SeparatedItemStringBuilder("{", ",", "}");
        } else {
            content = new SeparatedItemStringBuilder(q(name) + ":{", ",", "}");
        }

        if (outputNodeType) {
            content.append(q("type") + ":" + q(metaModel.getTypeName()));
        }

        for (PropertyMetaModel attributeMetaModel : attributes) {
            content.append(q(attributeMetaModel.getName()) + ":" + q(attributeMetaModel.getValue(node).toString()));
        }

        for (PropertyMetaModel subNodeMetaModel : subNodes) {
            Node value = (Node) subNodeMetaModel.getValue(node);
            if (value != null) {
                content.append(output(value, subNodeMetaModel.getName(), level + 1));
            }
        }

        for (PropertyMetaModel subListMetaModel : subLists) {
            NodeList<? extends Node> subList = (NodeList<? extends Node>) subListMetaModel.getValue(node);
            if (subList != null && !subList.isEmpty()) {
                SeparatedItemStringBuilder listContent = new SeparatedItemStringBuilder(q(subListMetaModel.getName()) + ":[", ",", "]");
                for (Node subListNode : subList) {
                    listContent.append(output(subListNode, null, level + 1));
                }
                content.append(listContent.toString());
            }
        }

        return content.toString();
    }

    private static String q(String value) {
        return "\"" + value + "\"";
    }
}
