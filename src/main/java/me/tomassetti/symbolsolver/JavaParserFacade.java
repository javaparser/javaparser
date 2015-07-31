package me.tomassetti.symbolsolver;

import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.MethodDeclaration;

/**
 * Class to be used by final users to solve symbols for JavaParser ASTs.
 */
public class JavaParserFacade {

    private TypeSolver typeSolver;
    private SymbolSolver symbolSolver;

    public JavaParserFacade(TypeSolver typeSolver) {
        this.typeSolver = typeSolver;
        this.symbolSolver = new SymbolSolver(typeSolver);
    }

    public SymbolReference solve(NameExpr nameExpr) {
        return symbolSolver.solveSymbol(nameExpr.getName(), nameExpr);
    }

    /**
     * Given a method call find out to which method declaration it corresponds.
     */
    public SymbolReference<MethodDeclaration> solve(MethodCallExpr methodCallExpr) {
        throw new UnsupportedOperationException();
    }

}
