package com.github.javaparser.utils;

import java.util.EnumSet;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;

/**
 * An implementation of JSON formatting.
 *
 * @version 3.1.0
 * @since 3.1.0
 * @see TreeStructureVisitor
 * @author Ryan Beckett
 *
 */

// TODO: json starts and ends with open and closing braces, so FormatInstructions
// needs a method to pre and post-add output to the final result
// TODO: current implementation adds comma to last property, which is not valid JSON

class JSONFormatInstructions implements FormatInstructions {

    @Override
    public String enterNode(Node n) {
        // TODO will this suffice? Are there any nodes other than CompilationUnit
        // with no parent?
        if (n.getParentNode() == null)
            return "{";
        return "\"" + n.getClass().getSimpleName() + "\": {";
    }

    @Override
    public String exitNode(Node n) {
        return "}, ";
    }

    @Override
    public String outputProperty(Node node, String name, EnumSet<Modifier> modifiers) {
        final StringBuilder sb = new StringBuilder("\"" + name + "\": [");
        modifiers.forEach(m -> sb.append("\"" + m.name() + "\", "));
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

}
