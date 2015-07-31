package me.tomassetti.symbolsolver.model;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;

/**
 * Created by federico on 28/07/15.
 */
public class SymbolSolver {

    private TypeSolver typeSolver;

    public SymbolSolver(TypeSolver typeSolver){
        if (typeSolver == null) throw new IllegalArgumentException();

        this.typeSolver = typeSolver;
    }

    public SymbolReference solveSymbol(String name, Context context) {
        return context.solveSymbol(name, typeSolver);
    }

    public SymbolReference solveSymbol(String name, Node node) {
        return solveSymbol(name, JavaParserFactory.getContext(node));
    }

    public SymbolReference<me.tomassetti.symbolsolver.model.TypeDeclaration> solveType(String name, Context context) {
        return context.solveType(name, typeSolver);
    }

    public SymbolReference<me.tomassetti.symbolsolver.model.TypeDeclaration> solveType(String name, Node node) {
        return solveType(name, JavaParserFactory.getContext(node));
    }
}
