package me.tomassetti.symbolsolver.model.usages.typesystem;

/**
 * @author Federico Tomassetti
 */
public class VoidType implements Type {
    public static final Type INSTANCE = new VoidType();

    private VoidType() {
    }

    @Override
    public String describe() {
        return "void";
    }

    @Override
    public boolean isAssignableBy(Type other) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isVoid() {
        return true;
    }
}
