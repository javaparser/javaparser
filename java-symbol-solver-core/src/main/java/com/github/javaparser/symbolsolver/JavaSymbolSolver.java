package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import com.github.javaparser.ast.type.ArrayType;


public class JavaSymbolSolver implements SymbolResolver {

    private TypeSolver typeSolver;

    public JavaSymbolSolver(TypeSolver typeSolver) {
        this.typeSolver = typeSolver;
    }

    @Override
    public <T> T resolve(Node node, Class<T> resultClass) {
        if (node instanceof MethodDeclaration) {
            return resultClass.cast(new JavaParserMethodDeclaration((MethodDeclaration)node, typeSolver));
        }
        if (node instanceof ArrayType) {
            return resultClass.cast(JavaParserFacade.get(typeSolver).convert((ArrayType)node, node));
        }
        throw new UnsupportedOperationException("Unable to resolve to " + resultClass.getSimpleName() + " from " + node.getClass().getSimpleName());
    }

    public void inject(CompilationUnit destination) {
        destination.setData(Node.SYMBOL_RESOLVER_KEY, this);
    }
}
