package me.tomassetti.symbolsolver.model.declarations;

/**
 * Created by federico on 19/08/15.
 */
public class AmbiguityException extends RuntimeException {
    private String description;

    public AmbiguityException(String description) {
        super(description);
    }
}
