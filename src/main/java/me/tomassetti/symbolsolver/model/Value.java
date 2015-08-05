package me.tomassetti.symbolsolver.model;

import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.lang.reflect.Type;

/**
 * Created by federico on 04/08/15.
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

    public String getName() {
        return name;
    }

    public boolean isField() {
        return field;
    }

    public TypeUsage getUsage() {
        return typeUsage;
    }

    public static Value from(ValueDeclaration decl, TypeSolver typeSolver) {
        return new Value(decl.getTypeUsage(typeSolver), decl.getName(), decl.isField());
    }
}
