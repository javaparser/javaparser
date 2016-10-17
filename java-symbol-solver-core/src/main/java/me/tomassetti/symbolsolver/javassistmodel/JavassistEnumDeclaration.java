package me.tomassetti.symbolsolver.javassistmodel;

import javassist.CtClass;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

import java.util.List;
import java.util.Set;

/**
 * @author Federico Tomassetti
 */
public class JavassistEnumDeclaration implements EnumDeclaration {

    private CtClass ctClass;
    private TypeSolver typeSolver;

    public JavassistEnumDeclaration(CtClass ctClass, TypeSolver typeSolver) {
        if (ctClass == null) {
            throw new IllegalArgumentException();
        }
        if (!ctClass.isEnum()) {
            throw new IllegalArgumentException("Trying to instantiate a JavassistEnumDeclaration with something which is not an enum: " + ctClass.toString());
        }
        this.ctClass = ctClass;
        this.typeSolver = typeSolver;
    }

    @Override
    public AccessLevel accessLevel() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getQualifiedName() {
        return ctClass.getName();
    }

    @Override
    public List<ReferenceType> getAncestors() {
        throw new UnsupportedOperationException();
    }

    @Override
    public FieldDeclaration getField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<FieldDeclaration> getAllFields() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<MethodUsage> getAllMethods() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAssignableBy(Type type) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return ctClass.getSimpleName();
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        throw new UnsupportedOperationException();
    }
}
