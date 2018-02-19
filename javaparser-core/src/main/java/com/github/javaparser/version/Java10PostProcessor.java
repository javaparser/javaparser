package com.github.javaparser.version;

import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.VarType;

import static com.github.javaparser.ParseResult.PostProcessor;

/**
 * Processes the generic AST into a Java 10 AST and validates it.
 */
public class Java10PostProcessor extends PostProcessors {
    protected final PostProcessor varNodeCreator = (result, configuration) ->
            result.getResult().ifPresent(node -> {
                node.findAll(ClassOrInterfaceType.class).forEach(n -> {
                    if (n.getNameAsString().equals("var")) {
                        n.replace(new VarType(n.getTokenRange().orElse(null)));
                    }
                });
            });

    public Java10PostProcessor() {
        add(varNodeCreator);
    }
}
