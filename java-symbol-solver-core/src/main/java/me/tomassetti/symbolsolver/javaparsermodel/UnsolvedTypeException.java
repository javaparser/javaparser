package me.tomassetti.symbolsolver.javaparsermodel;

import me.tomassetti.symbolsolver.model.resolution.Context;

/**
 * Created by federico on 30/07/15.
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
