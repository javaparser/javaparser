package com.github.javaparser.ast.jml;

import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.jml.JmlUtility;

import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/21)
 */
public interface NodeWithContracts<T extends Node> {

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    Optional<NodeList<JmlContract>> getContracts();

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    T setContracts(NodeList<JmlContract> contracts);

    default void addContracts(JmlContract contracts) {
        final var o = getContracts();
        if (o.isPresent()) {
            final var jmlContracts = o.get();
            jmlContracts.add(contracts);
            if (jmlContracts.size() == 1)
                JmlUtility.fixRangeContracts(this);
        } else {
            setContracts(new NodeList<>(contracts));
            JmlUtility.fixRangeContracts(this);
        }
    }
}
