package me.tomassetti.symbolsolver.javaparsermodel;

import me.tomassetti.symbolsolver.core.resolution.Context;

/**
 * @author Federico Tomassetti
 */
public class UnsolvedTypeException extends RuntimeException {

    private Context context;
    private String name;

    public UnsolvedTypeException(Context context, String name) {
        this.context = context;
        this.name = name;
    }

    @Override
    public String toString() {
        return "UnsolvedTypeException{" +
                "context=" + context +
                ", name='" + name + '\'' +
                '}';
    }
}
