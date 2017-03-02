package com.github.javaparser.utils.format;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.TreeStructureVisitor;

/**
 * An implementation of JSON formatting. Note that JSON doesn't allow duplicate keys,
 * and as a workaround we've appended indices (i.e. <i>Node, Node1, Node2</i>) to key names
 * that are equal and are members of the same JSON object.
 *
 * @version 3.1.0
 * @since 3.1.0
 * @see TreeStructureVisitor
 * @author Ryan Beckett
 *
 */

class JSONFormatInstructions implements FormatInstructions {

    private Map<Node, List<Node>> parentChildMap;

    public JSONFormatInstructions() {
        parentChildMap = new HashMap<>();
    }

    @Override
    public String enterNode(Node node) {
        String outputName = node.getClass().getSimpleName();
        Optional<Node> parent = node.getParentNode();
        if (!parent.isPresent())
            parentChildMap.put(node, new ArrayList<>());
        else {
            List<Node> childrenOfParent = parentChildMap.get(parent.get());
            int index = 0;
            for (int i = 0; i < childrenOfParent.size(); i++)
                if (childrenOfParent.get(i).getClass().getSimpleName().equals(outputName))
                    index++;
            if (index > 0)
                outputName += index;
            childrenOfParent.add(node);
            parentChildMap.put(node, new ArrayList<>());
        }
        return "\"" + outputName + "\": {";
    }

    @Override
    public String exitNode(Node node) {
        return "}, ";
    }

    @Override
    public String outputProperty(Node node, String name, List<String> contents) {
        final StringBuilder sb = new StringBuilder("\"" + name + "\": [");
        contents.forEach(c -> sb.append("\"" + c + "\", "));
        int index = sb.lastIndexOf(", ");
        if (index != -1)
            sb.delete(index, index + 2);
        sb.append("], ");
        return sb.toString();
    }

    @Override
    public String outputProperty(Node node, String name, String content) {
        return "\"" + name + "\": \"" + content + "\", ";
    }

    @Override
    public String postProcess(String result) {
        result = "{\n" + result + "\n}";
        StringBuilder sb = new StringBuilder();
        Pattern pattern = Pattern.compile(",\\s*\\}");
        Matcher matcher = pattern.matcher(result);
        int start = 0, tabs = -1;
        while (matcher.find()) {
            sb.append(result.substring(start, matcher.start()));
            sb.append("\n");
            tabs = matcher.group().split("\\t").length - 1;
            for (int i = 0; i < tabs; i++)
                sb.append("\t");
            sb.append("}");
            start = matcher.end();
        }
        return sb.toString().trim();
    }

}