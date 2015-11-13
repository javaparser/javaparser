package me.tomassetti.symbolsolver.model.typesystem;

public class VoidTypeUsage implements TypeUsage {
    public static final TypeUsage INSTANCE = new VoidTypeUsage();

    private VoidTypeUsage() {
    }

    @Override
    public String describe() {
        return "void";
    }

    @Override
    public boolean isAssignableBy(TypeUsage other) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isVoid() {
        return true;
    }
}
