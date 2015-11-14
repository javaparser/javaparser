package me.tomassetti.symbolsolver.model.resolution;

import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

/**
 * @author Federico Tomassetti
 */
public class Value {

    private TypeUsage typeUsage;
    private String name;
    private boolean field;

    public Value(TypeUsage typeUsage, String name, boolean field) {
        this.typeUsage = typeUsage;
        this.name = name;
        this.field = field;
    }

    public static Value from(ValueDeclaration decl, TypeSolver typeSolver) {
        TypeUsage typeUsage = decl.getType();
        return new Value(typeUsage, decl.getName(), decl.isField());
    }

    public String getName() {
        return name;
    }

    public boolean isField() {
        return field;
    }

    public TypeUsage getUsage() {
        return typeUsage;
    }

}
