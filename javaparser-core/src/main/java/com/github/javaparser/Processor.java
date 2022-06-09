package com.github.javaparser;

import com.github.javaparser.ast.Node;

public class Processor {
    /**
     * Makes the parser do a post-parsing step before the result is returned to the user.
     */
    public void postProcess(ParseResult<? extends Node> result, ParserConfiguration configuration) {
        
    }

    /**
     *  Adds a pre-parsing step, which has access to the sourcecode through the innerProvider.
     */
    public Provider preProcess(Provider innerProvider) {
        return innerProvider;
    }
}
