package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.symbolsolver.core.resolution.Context;

import java.util.Optional;

/**
 * @author Meghdoot Ojha
 */
public class ClientFactoryCall {
    public static void main(String[] args) {

        ContextHelper context= new ContextHelper() {

            public Optional<Context> getParent() {
                return Optional.empty();
            }
        };
        JavaParser parser=JavaParserFactory.getInstance
                (ContextHelper.
                        solveMethodAsUsage((ResolvedTypeDeclaration) context));
        parser.getContext();
    }

}
