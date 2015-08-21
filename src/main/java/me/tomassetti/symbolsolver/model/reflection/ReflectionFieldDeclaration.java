package me.tomassetti.symbolsolver.model.reflection;

import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.lang.reflect.Field;

/**
 * Created by federico on 19/08/15.
 */
public class ReflectionFieldDeclaration implements FieldDeclaration {

    public ReflectionFieldDeclaration(Field field) {
        this.field = field;
    }

    private Field field;

    @Override
    public TypeUsage getType(TypeSolver typeSolver) {
        // TODO consider interfaces, enums, primitive types, arrays
        return ReflectionFactory.typeUsageFor(field.getType());
    }

    @Override
    public String getName() {
        return field.getName();
    }

    @Override
    public boolean isField() {
        return true;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isVariable() {
        return false;
    }

    @Override
    public boolean isType() {
        return false;
    }
}
