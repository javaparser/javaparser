package com.github.javaparser.utils.format;

import java.util.List;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.TreeStructureVisitor;

/**
 * An implementation of XML formatting.
 *
 * @version 3.1.0
 * @since 3.1.0
 * @see TreeStructureVisitor
 * @author Ryan Beckett
 *
 */
class XMLFormatInstructions implements FormatInstructions {

    @Override
    public String enterNode(Node node) {
        return "<" + node.getClass().getSimpleName() + ">";
    }

    @Override
    public String exitNode(Node node) {
        return "</" + node.getClass().getSimpleName() + ">";
    }

    @Override
    public String outputProperty(Node node, String name, List<String> contents) {
        final StringBuilder sb = new StringBuilder("<" + name + ">");
        contents.forEach(c -> sb.append(c + ", "));
        int index = sb.lastIndexOf(", ");
        if (index != -1)
            sb.delete(index, index + 2);
        sb.append("</" + name + ">");
        return sb.toString();
    }

    @Override
    public String outputProperty(Node node, String name, String content) {
        return "<" + name + ">" + content + "</" + name + ">";
    }

    @Override
    public String postProcess(String result) {
        return result;
    }
}
