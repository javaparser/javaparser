package com.github.javaparser.ast.validator;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.Node;

import java.util.function.BiConsumer;

/**
 * A validator that validates a known node type.
 */
public interface TypedValidator<N extends Node> extends BiConsumer<N, ProblemReporter> {
    /**
     * @param node the node that wants to be validated
     * @param problemReporter when found, validation errors can be reported here
     */
    void accept(N node, ProblemReporter problemReporter);

    @SuppressWarnings("unchecked")
    default ParseResult.PostProcessor postProcessor() {
        return (result, configuration) ->
                result.getResult().ifPresent(node ->
                        accept((N) node, new ProblemReporter(problem -> result.getProblems().add(problem))));
    }
}
