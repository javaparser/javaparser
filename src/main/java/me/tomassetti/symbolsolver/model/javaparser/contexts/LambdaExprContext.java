package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.LambdaExpr;
import me.tomassetti.symbolsolver.model.SymbolDeclarator;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;

import java.util.List;

/**
 * Created by federico on 28/07/15.
 */
public class LambdaExprContext extends AbstractJavaParserContext<LambdaExpr> {


    public LambdaExprContext(LambdaExpr wrappedNode) {
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
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        return getParent().solveType(name, typeSolver);
    }

    @Override
    public SymbolReference<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, parameterTypes, typeSolver);
    }

}
