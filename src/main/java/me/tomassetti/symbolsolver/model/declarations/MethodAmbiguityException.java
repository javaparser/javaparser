package me.tomassetti.symbolsolver.model.declarations;

/**
 * It is not possible to decide how to resolve a method invocation.
 *
 * @author Federico Tomassetti
 */
public class MethodAmbiguityException extends RuntimeException {
    public MethodAmbiguityException(String description) {
        super(description);
    }
}
