package me.tomassetti.symbolsolver.model.javassist;

import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.model.TypeParameter;
import me.tomassetti.symbolsolver.model.TypeSolver;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by federico on 05/08/15.
 */
public class JavassistTypeParameter implements TypeParameter {

    private SignatureAttribute.TypeParameter wrapped;
    private boolean declaredOnClass;

    @Override
    public String toString() {
        return "JavassistTypeParameter{" +
                wrapped.getName()
                +'}';
    }

    public JavassistTypeParameter(SignatureAttribute.TypeParameter wrapped, boolean declaredOnClass) {
        this.wrapped = wrapped;
        this.declaredOnClass = declaredOnClass;
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
        throw new UnsupportedOperationException();
    }

    @Override
    public String getQNameOfDeclaringClass() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<Bound> getBounds(TypeSolver typeSolver) {
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
