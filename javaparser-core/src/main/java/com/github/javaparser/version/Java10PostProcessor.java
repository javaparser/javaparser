package com.github.javaparser.version;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.validator.Java10Validator;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;

/**
 * Processes the generic AST into a Java 10 AST and validates it.
 */
public class Java10PostProcessor implements ParseResult.PostProcessor {
    private final Java10Validator validator = new Java10Validator();

    @Override
    public void process(ParseResult<? extends Node> result, ParserConfiguration configuration) {
        result.getResult().ifPresent(node -> {
            node.findAll(ClassOrInterfaceType.class).forEach(n -> {
                if (n.getNameAsString().equals("var")) {
                    n.replace(new VarType(n.getTokenRange().orElse(null)));
                }
            });
            validator.accept(node, new ProblemReporter(problem -> result.getProblems().add(problem)));
        });
    }
}
