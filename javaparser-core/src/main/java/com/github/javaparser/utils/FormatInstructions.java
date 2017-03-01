package com.github.javaparser.utils;

import java.util.EnumSet;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;

/**
 * An interface for defining a formatting scheme to be used with {@link TreeStructureVisitor}.
 * See {@link XMLFormatInstructions} for an example of how to implement a format.
 *
 * @version 3.1.0
 * @since 3.1.0
 * @see TreeStructureVisitor
 * @author Ryan Beckett
 *
 */
public interface FormatInstructions {

    public abstract String enterNode(Node n);

    public abstract String exitNode(Node n);

    public abstract String outputProperty(Node node, String name, EnumSet<Modifier> modifiers);

    public abstract String outputProperty(Node node, String name, String content);

    // public abstract void finalize(PrintStream printStream);
}
