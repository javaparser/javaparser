package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.Type;

import java.lang.reflect.Field;

public class ReflectionFieldDeclaration implements FieldDeclaration {

    private Field field;
    private TypeSolver typeSolver;
    private Type type;

    public ReflectionFieldDeclaration(Field field, TypeSolver typeSolver) {
        this.field = field;
        this.typeSolver = typeSolver;
        this.type = calcType();
    }

    private ReflectionFieldDeclaration(Field field, TypeSolver typeSolver, Type type) {
        this.field = field;
        this.typeSolver = typeSolver;
        this.type = type;
    }

    @Override
    public Type getType() {
        return type;
    }

    private Type calcType() {
        // TODO consider interfaces, enums, primitive types, arrays
        return ReflectionFactory.typeUsageFor(field.getGenericType(), typeSolver);
    }

    @Override
    public String getName() {
        return field.getName();
    }

    @Override
    public boolean isField() {
        return true;
    }

    public FieldDeclaration replaceType(Type fieldType) {
        return new ReflectionFieldDeclaration(field, typeSolver, fieldType);
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isType() {
        return false;
    }
}
