package com.github.javaparser.utils;

import java.util.EnumSet;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;

/**
 * An implementation for the default formatting scheme.
 *
 * @version 3.1.0
 * @since 3.1.0
 * @see TreeStructureVisitor
 * @author Ryan Beckett
 *
 */
class DefaultFormatInstructions implements FormatInstructions {

    @Override
    public String enterNode(Node n) {
        return n.getClass().getSimpleName();
    }

    @Override
    public String exitNode(Node n) {
        return "";
    }

    @Override
    public String outputProperty(Node node, String name, EnumSet<Modifier> modifiers) {
        return name + ": " + modifiers;
    }

    @Override
    public String outputProperty(Node node, String name, String content) {
        return name + ": " + content;
    }

}
