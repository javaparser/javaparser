package me.tomassetti.symbolsolver.model.javassist;

import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.model.TypeParameter;

/**
 * Created by federico on 05/08/15.
 */
public class JavassistTypeParameter implements TypeParameter {

    private SignatureAttribute.TypeParameter wrapped;

    public JavassistTypeParameter(SignatureAttribute.TypeParameter wrapped) {
        this.wrapped = wrapped;
    }

    @Override
    public String getName() {
        return wrapped.getName();
    }

    @Override
    public boolean declaredOnClass() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean declaredOnMethod() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getQNameOfDeclaringClass() {
        throw new UnsupportedOperationException();
    }
}
