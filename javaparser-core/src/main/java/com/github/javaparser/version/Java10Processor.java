package com.github.javaparser.version;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;

/**
 * Processes the generic AST into a Java 10 AST and validates it.
 */
public class Java10Processor implements ParseResult.PostProcessor {
    @Override
    public void process(ParseResult<? extends Node> result, ParserConfiguration configuration) {
        result.getResult().get().accept(
                new ModifierVisitor<Void>() {
                    @Override
                    public Visitable visit(ClassOrInterfaceType n, Void arg) {
                        if (n.getNameAsString().equals("var")) {
                            return new VarType(n.getTokenRange().orElse(null));
                        }
                        return super.visit(n, arg);
                    }
                }, null);
    }
}
