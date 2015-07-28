package me.tomassetti.symbolsolver.model;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;

/**
 * Created by federico on 28/07/15.
 */
public class SymbolSolver {

    private TypeSolver typeSolver;

    public SymbolSolver() {

    }

    public SymbolSolver(TypeSolver typeSolver){
        this.typeSolver = typeSolver;
    }

    public SymbolReference solveSymbol(String name, Context context) {
        return context.solveSymbol(name, typeSolver);
    }

    public SymbolReference solveSymbol(String name, Node node) {
        return solveSymbol(name, JavaParserFactory.getContext(node));
    }
}
