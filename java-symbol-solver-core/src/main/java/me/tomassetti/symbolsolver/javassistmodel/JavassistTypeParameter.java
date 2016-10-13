package me.tomassetti.symbolsolver.javassistmodel;

import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.model.resolution.TypeParameter;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

import java.util.ArrayList;
import java.util.List;

public class JavassistTypeParameter implements TypeParameter {

    private SignatureAttribute.TypeParameter wrapped;
    private boolean declaredOnClass;
    private TypeSolver typeSolver;

    public JavassistTypeParameter(SignatureAttribute.TypeParameter wrapped, boolean declaredOnClass, TypeSolver typeSolver) {
        this.wrapped = wrapped;
        this.declaredOnClass = declaredOnClass;
        this.typeSolver = typeSolver;
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
    public String qualifiedName() {
        if (this.declaredOnClass()) {
            throw new UnsupportedOperationException();
            //return String.format("%s.%s", getQNameOfDeclaringClass(), getName());
        } else {
            //com.github.javaparser.ast.body.MethodDeclaration jpMethodDeclaration = (com.github.javaparser.ast.body.MethodDeclaration)wrappedNode.getParentNode();
            //MethodDeclaration methodDeclaration = new JavaParserMethodDeclaration(jpMethodDeclaration, typeSolver());
            //return String.format("%s.%s", methodDeclaration.getQualifiedSignature(), getName());
            throw new UnsupportedOperationException();
        }
    }


    @Override
    public List<TypeParameter.Bound> getBounds(TypeSolver typeSolver) {
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
