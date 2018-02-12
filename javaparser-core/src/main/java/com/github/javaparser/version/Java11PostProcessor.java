package com.github.javaparser.version;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.validator.Java11Validator;
import com.github.javaparser.ast.validator.ProblemReporter;

/**
 * Processes the generic AST into a Java 10 AST and validates it.
 */
public class Java11PostProcessor extends Java10PostProcessor {
    protected final ParseResult.PostProcessor java11Validator = new Java11Validator().postProcessor();

    public Java11PostProcessor() {
        replace(java10Validator, java11Validator);
    }
}
