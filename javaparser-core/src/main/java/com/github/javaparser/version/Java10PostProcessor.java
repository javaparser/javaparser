package com.github.javaparser.version;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.validator.Java10Validator;
import com.github.javaparser.ast.validator.ProblemReporter;

import static com.github.javaparser.ParseResult.*;

/**
 * Processes the generic AST into a Java 10 AST and validates it.
 */
public class Java10PostProcessor extends PostProcessors {
    protected final PostProcessor java10Validator = new Java10Validator().postProcessor();
    protected final PostProcessor varNodeCreator = new PostProcessor() {
        @Override
        public void process(ParseResult<? extends Node> result, ParserConfiguration configuration) {
            result.getResult().ifPresent(node -> {
                node.findAll(ClassOrInterfaceType.class).forEach(n -> {
                    if (n.getNameAsString().equals("var")) {
                        n.replace(new VarType(n.getTokenRange().orElse(null)));
                    }
                });
            });
        }
    };

    public Java10PostProcessor() {
        add(varNodeCreator);
        add(java10Validator);
    }
}
