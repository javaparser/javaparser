package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

/**
 * This implementation of the SymbolResolver wraps the functionalities of the library to make them easily usable
 * from JavaParser nodes.
 *
 * An instance of this class should be created once and then injected in all the CompilationUnit for which we
 * want to enable symbol resolution. To do so the method inject can be used.
 *
 * @author Federico Tomassetti
 */
public class JavaSymbolSolver implements SymbolResolver {

    private TypeSolver typeSolver;

    public JavaSymbolSolver(TypeSolver typeSolver) {
        this.typeSolver = typeSolver;
    }

    /**
     * Register this SymbolResolver into a CompilationUnit, so that symbol resolution becomes available to
     * all nodes part of the CompilationUnit.
     */
    public void inject(CompilationUnit destination) {
        destination.setData(Node.SYMBOL_RESOLVER_KEY, this);
    }

    @Override
    public <T> T resolveDeclaration(Node node, Class<T> resultClass) {
        if (node instanceof MethodDeclaration) {
            return resultClass.cast(new JavaParserMethodDeclaration((MethodDeclaration)node, typeSolver));
        }
        throw new UnsupportedOperationException("Unable to find the declaration of type " + resultClass.getSimpleName()
                + " from " + node.getClass().getSimpleName());
    }

    @Override
    public <T> T toResolvedType(Type javaparserType, Class<T> resultClass) {
        if (javaparserType instanceof ArrayType) {
            return resultClass.cast(JavaParserFacade.get(typeSolver).convert((ArrayType)javaparserType, javaparserType));
        }
        throw new UnsupportedOperationException("Unable to get the resolved type of class "
                + resultClass.getSimpleName() + " from " + javaparserType);
    }

    @Override
    public ResolvedType calculateType(Expression expression) {
        throw new UnsupportedOperationException("Unable to calculate type of " + expression);
    }
}
