package me.tomassetti.symbolsolver.resolution.javaparser;

import me.tomassetti.symbolsolver.resolution.Context;

public class UnsolvedSymbolException extends RuntimeException {

    private String context;
    private String name;

    @Override
    public String toString() {
        return "UnsolvedSymbolException{" +
                "context=" + context +
                ", name='" + name + '\'' +
                '}';
    }

    public UnsolvedSymbolException(Context context, String name) {
        super("Unsolved symbol in "+context+" : "+name);
        this.context = context.toString();
        this.name = name;
    }

    public UnsolvedSymbolException(String context, String name) {
        super("Unsolved symbol in "+context+" : "+name);
        this.context = context;
        this.name = name;
    }

    public UnsolvedSymbolException(String name) {
        super("Unsolved symbol : "+name);
        this.context = "unknown";
        this.name = name;
    }
}
