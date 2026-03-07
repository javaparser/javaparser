package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.key.KeyCcatchReturn;
import com.github.javaparser.resolution.SymbolDeclarator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

public class KeyCcatchReturnContext extends AbstractJavaParserContext<KeyCcatchReturn> {
    public KeyCcatchReturnContext(KeyCcatchReturn kcr, TypeSolver typeSolver) {
        super(kcr, typeSolver);
    }

    @Override
    public final SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        if (wrappedNode.getParameter().isPresent()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(
                    wrappedNode.getParameter().get(), typeSolver);
            SymbolReference<? extends ResolvedValueDeclaration> symbolReference =
                    AbstractJavaParserContext.solveWith(sb, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return solveSymbolInParentContext(name);
    }

    @Override
    public final Optional<Value> solveSymbolAsValue(String name) {
        if (wrappedNode.getParameter().isPresent()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(
                    wrappedNode.getParameter().get(), typeSolver);
            Optional<Value> symbolReference = solveWithAsValue(sb, name);
            if (symbolReference.isPresent()) {
                // Perform parameter type substitution as needed
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return solveSymbolAsValueInParentContext(name);
    }

    @Override
    public final SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name,
            List<ResolvedType> argumentsTypes,
            boolean staticOnly,
            ResolvedReferenceTypeDeclaration invocationContext) {
        // TODO: Document why staticOnly is forced to be false.
        return solveMethodInParentContext(name, argumentsTypes, false, invocationContext);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        return Collections.emptyList();
    }

    @Override
    public List<Parameter> parametersExposedToChild(Node child) {
        // TODO/FIXME: Presumably the parameters must be exposed to all children and their descendants, not just the
        // direct child?
        if (getWrappedNode().getParameter().isPresent()
                && getWrappedNode().getBlock().isPresent()
                && child == getWrappedNode().getBlock().get()) {
            return Collections.singletonList(getWrappedNode().getParameter().get());
        }
        return Collections.emptyList();
    }
}
