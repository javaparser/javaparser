package com.github.javaparser.ast.visitor.treestructure;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

import java.util.EnumSet;

import static com.github.javaparser.utils.Utils.EOL;
import static com.github.javaparser.utils.Utils.indent;

public class TreeStructureDumpCallback implements TreeStructureVisitor.Callback {
    private final StringBuilder builder;

    public TreeStructureDumpCallback(StringBuilder builder) {
        this.builder = builder;
    }

    private void printIndented(int indentLevel, String text) {
        indent(builder, indentLevel).append(text).append(EOL);
    }

    @Override
    public void exitNode(Node n, String name, Integer indent) {
    }

    @Override
    public void enterNode(Node n, String name, Integer indent) {
        printIndented(indent, name + " (" + n.getClass().getSimpleName() + ")");
    }

    @Override
    public void outputProperty(Node node, String name, EnumSet<Modifier> modifiers, Integer indent) {
        printIndented(indent, name + ": " + modifiers);
    }

    @Override
    public void outputProperty(Node node, String name, Enum<?> e, Integer indent) {
        printIndented(indent, name + ": " + e);
    }

    @Override
    public void outputProperty(Node node, String name, String content, Integer indent) {
        printIndented(indent, name + ": " + content);
    }

    @Override
    public void outputProperty(Node node, String name, boolean value, Integer indent) {
        printIndented(indent, name + ": " + value);
    }

    @Override
    public void enterList(NodeList n, String name, int indent) {
    }

    @Override
    public void exitList(NodeList n, String name, int indent) {
    }
}
