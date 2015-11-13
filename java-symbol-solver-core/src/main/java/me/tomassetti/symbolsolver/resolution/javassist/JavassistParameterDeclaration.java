package me.tomassetti.symbolsolver.resolution.javassist;

import javassist.CtClass;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.TypeSolver;


/**
 * Created by federico on 02/08/15.
 */
public class JavassistParameterDeclaration implements ParameterDeclaration {
    private CtClass type;
    private TypeSolver typeSolver;
    public JavassistParameterDeclaration(CtClass type, TypeSolver typeSolver) {

        this.type = type;
        this.typeSolver = typeSolver;
    }

    @Override
    public String toString() {
        return "JavassistParameterDeclaration{" +
                "type=" + type +
                '}';
    }

    @Override
    public String getName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isField() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isParameter() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeUsage getType() {
        return JavassistFactory.typeUsageFor(type, typeSolver);
    }
}
