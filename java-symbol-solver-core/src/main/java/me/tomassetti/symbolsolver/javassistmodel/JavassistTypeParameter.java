package me.tomassetti.symbolsolver.javassistmodel;

import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

import java.util.ArrayList;
import java.util.List;

public class JavassistTypeParameter implements TypeParameterDeclaration {

    private SignatureAttribute.TypeParameter wrapped;
    private boolean declaredOnClass;
    private TypeSolver typeSolver;
    private String qualifier;

    public JavassistTypeParameter(SignatureAttribute.TypeParameter wrapped, boolean declaredOnClass, String qualifier, TypeSolver typeSolver) {
        this.wrapped = wrapped;
        this.declaredOnClass = declaredOnClass;
        this.typeSolver = typeSolver;
        this.qualifier = qualifier;
    }

    @Override
    public String toString() {
        return "JavassistTypeParameter{" +
                wrapped.getName()
                + '}';
    }

    @Override
    public String getName() {
        return wrapped.getName();
    }

    @Override
    public boolean declaredOnClass() {
        return declaredOnClass;
    }

    @Override
    public boolean declaredOnMethod() {
        return !declaredOnClass();
    }

    @Override
    public String getQualifiedName() {
        return String.format("%s.%s", qualifier, getName());
    }

    @Override
    public List<TypeParameterDeclaration.Bound> getBounds(TypeSolver typeSolver) {
        List<Bound> bounds = new ArrayList<>();
        if (wrapped.getClassBound() != null) {
            throw new UnsupportedOperationException(wrapped.getClassBound().toString());
        }
        for (SignatureAttribute.ObjectType ot : wrapped.getInterfaceBound()) {
            throw new UnsupportedOperationException(ot.toString());
        }
        return bounds;
    }
}
