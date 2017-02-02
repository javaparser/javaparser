package com.github.javaparser.ast.visitor.treestructure;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

import java.util.EnumSet;
import java.util.Stack;

/**
 * A basic JSON output callback for the TreeStructureVisitor.
 */
public class TreeStructureJsonCallback implements TreeStructureVisitor.Callback {
    private static class State {
        public boolean firstProperty = true;
    }

    private final StringBuilder builder;
    private final boolean outputNodeType;
    private final Stack<State> stateStack = new Stack<>();

    public TreeStructureJsonCallback(StringBuilder builder, boolean outputNodeType) {
        this.builder = builder;
        this.outputNodeType = outputNodeType;
    }

    @Override
    public void enterNode(Node n, String name, Integer indent) {
        if(name.equals("root")){
            builder.append("{");
        }
        comma();
        stateStack.push(new State());
        builder.append("\"").append(name).append("\"").append(":").append("{");
        if (outputNodeType) {
            printAttribute("type", n.getClass().getSimpleName());
        }
    }

    @Override
    public void exitNode(Node n, String name, Integer indent) {
        builder.append("}");
        stateStack.pop();
        if(name.equals("root")){
            builder.append("}");
        }
    }

    private void printAttribute(String name, String value) {
        comma();
        builder.append("\"").append(name).append("\":\"").append(value).append("\"");
    }

    private void comma() {
        if(stateStack.isEmpty()){
            return;
        }
        State state = stateStack.peek();
        if (!state.firstProperty) {
            builder.append(",");
        }
        state.firstProperty = false;
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

    @Override
    public void enterList(NodeList n, String name, int indent) {
        
    }

    @Override
    public void exitList(NodeList n, String name, int indent) {

    }
}
