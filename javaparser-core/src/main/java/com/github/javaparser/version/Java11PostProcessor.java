package com.github.javaparser.version;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.validator.Java10Validator;
import com.github.javaparser.ast.validator.Java11Validator;
import com.github.javaparser.ast.validator.ProblemReporter;

/**
 * Processes the generic AST into a Java 10 AST and validates it.
 */
public class Java11PostProcessor extends Java10PostProcessor {
    private final Java11Validator validator = new Java11Validator();

    @Override
    public void process(ParseResult<? extends Node> result, ParserConfiguration configuration) {
        result.getResult().ifPresent(node ->
                validator.accept(node, new ProblemReporter(problem -> result.getProblems().add(problem))));
    }
}
