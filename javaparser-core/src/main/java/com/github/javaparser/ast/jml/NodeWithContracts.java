package com.github.javaparser.ast.jml;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.jml.JmlUtility;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/21)
 */
public interface NodeWithContracts<T extends Node> {

    NodeList<JmlContract> getContracts();

    T setContracts(NodeList<JmlContract> contracts);

    default void addContracts(JmlContract contracts) {
        final var jmlContracts = getContracts();
        jmlContracts.add(contracts);
        if (jmlContracts.size() == 1) JmlUtility.fixRangeContracts(this);
    }
}
