package com.github.javaparser.ast;

/**
 * A node having a name.
 *  
 * The main reason for this interface is to permit users to manipulate homogeneously all nodes with a getName method.
 * 
 * @since 2.0.1 
 */
public interface NamedNode {
    String getName();
}
