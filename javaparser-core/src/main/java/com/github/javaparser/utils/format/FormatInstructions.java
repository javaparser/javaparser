package com.github.javaparser.utils.format;

import java.util.List;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.TreeStructureVisitor;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

/**
 * An interface for defining formatting instructions to be used with {@link TreeStructureVisitor}.
 * See {@link XMLFormatInstructions} for an example of how to implement a format.
 * <br/>
 * <br/>
 * Since not all formats lend themselves to be easily implemented via a visitor pattern, we
 * provide {@link #postProcess(StringBuilder)} to allow post-processing of the resultant string.
 * See {@link JSONFormatInstructions} for an example of post-processing.
 *
 * @version 3.1.0
 * @since 3.1.0
 * @see TreeStructureVisitor
 * @see BaseNodeMetaModel
 * @author Ryan Beckett
 *
 */
public interface FormatInstructions {

    /**
     * Define the string to be output when a node of the AST is entered.
     *
     * @param node The currently visited node of the AST.
     * @return The formatted output string.
     * @see BaseNodeMetaModel
     */
    public abstract String enterNode(Node node);

    /**
     * Define the string to be output when a node of the AST is exited.
     *
     * @param node The currently visited node of the AST.
     * @return The formatted output string.
     * @see BaseNodeMetaModel
     */
    public abstract String exitNode(Node node);

    /**
     * Define the string to be output when a multi-valued property of a node of the AST is incurred.
     *
     * @param node The currently visited node of the AST that contains the property.
     * @param name The name of the property.
     * @param contents A list of values for the property.
     * @return The formatted output string.
     * @see PropertyMetaModel
     */
    public abstract String outputProperty(Node node, String name, List<String> contents);

    /**
     * Define the string to be output when a property of a node of the AST is incurred.
     *
     * @param node The currently visited node of the AST that contains the property.
     * @param name The name of the property.
     * @param content The value for the property.
     * @return The formatted output string.
     * @see PropertyMetaModel
     */
    public abstract String outputProperty(Node node, String name, String content);

    /**
     * Allow for post-processing modifications of the formatted string generated after
     * running the visitor. This method is called before {@link TreeStructureVisitor#getResult()}
     * returns.
     *
     * @param result The formatted string generated from the visitor.
     * @return The finalized formatted output string after post-processing.
     */
    public abstract String postProcess(String result);
}
