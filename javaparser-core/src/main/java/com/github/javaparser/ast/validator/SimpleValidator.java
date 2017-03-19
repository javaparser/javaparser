package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;

import java.util.function.BiConsumer;
import java.util.function.Predicate;

/**
 * Runs a validator on all nodes of a certain type,
 * and adds a problem for all nodes that pass a condition.
 */
public class SimpleValidator<N extends Node> implements Validator {
    private final Class<N> type;
    private final TypedValidator<N> validator;

    public SimpleValidator(Class<N> type, Predicate<N> condition, BiConsumer<N, ProblemReporter> problemSupplier) {
        this.type = type;
        this.validator = (node, problemReporter) -> {
            if (condition.test(node)) {
                problemSupplier.accept(node, problemReporter);
            }
        };
    }

    @Override
    public void accept(Node node, ProblemReporter problemReporter) {
        node.getNodesByType(type).forEach(n -> validator.accept(n, problemReporter));
    }
}
