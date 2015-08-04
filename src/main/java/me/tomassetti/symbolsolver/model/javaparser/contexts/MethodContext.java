package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.body.MethodDeclaration;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 28/07/15.
 */
public class MethodContext extends AbstractJavaParserContext<MethodDeclaration> {


    public MethodContext(MethodDeclaration wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public SymbolReference<ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            SymbolReference symbolReference = solveWith(sb, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            Optional<Value> symbolReference = solveWithAsValue(sb, name, typeSolver);
            if (symbolReference.isPresent()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        return getParent().solveType(name, typeSolver);
    }

    @Override
    public SymbolReference<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        if (wrappedNode.getName().equals(name)) {
            // TODO understand if signature is compatible
            throw new UnsupportedOperationException();
        }

        return getParent().solveMethod(name, parameterTypes, typeSolver);
    }

}
