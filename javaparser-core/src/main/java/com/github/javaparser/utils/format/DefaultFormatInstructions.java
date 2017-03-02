package com.github.javaparser.utils.format;

import java.util.List;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.TreeStructureVisitor;

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
    public String enterNode(Node node) {
        return node.getClass().getSimpleName();
    }

    @Override
    public String exitNode(Node node) {
        return "";
    }

    @Override
    public String outputProperty(Node node, String name, List<String> contents) {
        return name + ": " + contents;
    }

    @Override
    public String outputProperty(Node node, String name, String content) {
        return name + ": " + content;
    }

    @Override
    public String postProcess(String result) {
        return result;
    }

}
