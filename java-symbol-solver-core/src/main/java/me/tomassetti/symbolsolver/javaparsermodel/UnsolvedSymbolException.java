package me.tomassetti.symbolsolver.javaparsermodel;

import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

// Use the one in model instead
@Deprecated
public class UnsolvedSymbolException extends RuntimeException {

    private String context;
    private String name;
    private TypeSolver typeSolver;

    public UnsolvedSymbolException(String name, TypeSolver typeSolver) {
        super("Unsolved symbol : " + name + " using typesolver " + typeSolver);
        this.typeSolver = typeSolver;
        this.name = name;
    }

    public UnsolvedSymbolException(Context context, String name) {
        super("Unsolved symbol in " + context + " : " + name);
        this.context = context.toString();
        this.name = name;
    }

    public UnsolvedSymbolException(String context, String name) {
        super("Unsolved symbol in " + context + " : " + name);
        this.context = context;
        this.name = name;
    }

    public UnsolvedSymbolException(String name) {
        super("Unsolved symbol : " + name);
        this.context = "unknown";
        this.name = name;
    }

    @Override
    public String toString() {
        return "UnsolvedSymbolException{" +
                "context='" + context + '\'' +
                ", name='" + name + '\'' +
                ", typeSolver=" + typeSolver +
                '}';
    }
}
