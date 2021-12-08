package com.github.javaparser.ast.jml;

import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.jml.clauses.JmlContracts;
import com.github.javaparser.ast.stmt.ForStmt;

import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/21)
 */
public interface NodeWithContracts<T> {
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    Optional<NodeList<JmlContracts>> getContracts();

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    T setContracts(NodeList<JmlContracts> contracts);

    default void addContracts(JmlContracts contracts) {
        if (getContracts().isPresent()) {
            getContracts().get().add(contracts);
        } else {
            setContracts(new NodeList<>(contracts));
        }
    }
}
