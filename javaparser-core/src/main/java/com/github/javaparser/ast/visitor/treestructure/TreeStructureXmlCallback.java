package com.github.javaparser.ast.visitor.treestructure;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;

import java.util.EnumSet;

/**
 * A basic XML output callback for the TreeStructureVisitor.
 */
public class TreeStructureXmlCallback implements TreeStructureVisitor.Callback {
    private final StringBuilder builder;
    private final boolean outputNodeType;
    private boolean inOpenTag = false;

    public TreeStructureXmlCallback(StringBuilder builder, boolean outputNodeType) {
        this.builder = builder;
        this.outputNodeType = outputNodeType;
    }

    @Override
    public void enterNode(Node n, String name, Integer indent) {
        endOpenTag();
        builder.append("<").append(name);
        inOpenTag = true;
        if (outputNodeType) {
            printAttribute("type", n.getClass().getSimpleName());
        }
    }

    @Override
    public void exitNode(Node n, String name, Integer indent) {
        endOpenTag();
        builder.append("</").append(name).append(">");
    }

    private void endOpenTag() {
        if (inOpenTag) {
            builder.append(">");
            inOpenTag = false;
        }
    }

    private void printAttribute(String name, String value) {
        builder.append(" ").append(name).append("='").append(value).append("'");
    }

    @Override
    public void outputProperty(Node node, String name, EnumSet<Modifier> modifiers, Integer indent) {
        printAttribute(name, modifiers.toString());
    }

    @Override
    public void outputProperty(Node node, String name, Enum<?> e, Integer indent) {
        printAttribute(name, e.name());
    }

    @Override
    public void outputProperty(Node node, String name, String content, Integer indent) {
        printAttribute(name, content);
    }

    @Override
    public void outputProperty(Node node, String name, boolean value, Integer indent) {
        printAttribute(name, Boolean.toString(value));
    }
}
