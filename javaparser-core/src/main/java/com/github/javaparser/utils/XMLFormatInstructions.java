package com.github.javaparser.utils;

import java.util.EnumSet;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;

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
    public String enterNode(Node n) {
        return "<" + n.getClass().getSimpleName() + ">";
    }

    @Override
    public String exitNode(Node n) {
        return "</" + n.getClass().getSimpleName() + ">";
    }

    @Override
    public String outputProperty(Node node, String name, EnumSet<Modifier> modifiers) {
        final StringBuilder sb = new StringBuilder("<" + name + ">");
        modifiers.forEach(m -> sb.append(m.name() + ", "));
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

}
