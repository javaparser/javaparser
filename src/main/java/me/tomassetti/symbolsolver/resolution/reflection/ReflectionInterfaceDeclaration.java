package me.tomassetti.symbolsolver.resolution.reflection;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.logic.AbstractTypeDeclaration;
import me.tomassetti.symbolsolver.logic.MethodResolutionLogic;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.typesystem.NullTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.Context;
import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeParameter;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.javaparser.LambdaArgumentTypeUsagePlaceholder;
import me.tomassetti.symbolsolver.resolution.javaparser.UnsolvedSymbolException;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.TypeVariable;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class ReflectionInterfaceDeclaration extends AbstractTypeDeclaration implements InterfaceDeclaration {

    private Class<?> clazz;
    private TypeSolver typeSolver;

    public ReflectionInterfaceDeclaration(Class<?> clazz, TypeSolver typeSolver) {
        if (!clazz.isInterface()) {
            throw new IllegalArgumentException();
        }

        this.clazz = clazz;
        this.typeSolver = typeSolver;
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeUsage(other, typeSolver));
    }

    @Override
    public String getQualifiedName() {
        return clazz.getCanonicalName();
    }

    @Override
    public Context getContext() {
        return new ClassOrInterfaceDeclarationContext(clazz);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes) {
        List<MethodDeclaration> methods = new ArrayList<>();
        for (Method method : clazz.getMethods()) {
            if (method.isBridge() || method.isSynthetic()) continue;
            MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            methods.add(methodDeclaration);
        }
        return MethodResolutionLogic.findMostApplicable(methods, name, parameterTypes, typeSolver);
    }

    @Override
    public String toString() {
        return "ReflectionClassDeclaration{" +
                "clazz=" + clazz.getCanonicalName() +
                '}';
    }

    public TypeUsage getUsage(Node node) {
        return new ReferenceTypeUsage(this, typeSolver);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ReflectionInterfaceDeclaration)) return false;

        ReflectionInterfaceDeclaration that = (ReflectionInterfaceDeclaration) o;

        if (!clazz.getCanonicalName().equals(that.clazz.getCanonicalName())) return false;

        if (!getTypeParameters().equals(that.getTypeParameters())) {
            return false;
        }

        return true;
    }

    @Override
    public int hashCode() {
        return clazz.hashCode();
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext, List<TypeUsage> typeParameterValues) {
        if (typeParameterValues.size() != getTypeParameters().size()) {
            //if (typeParameterValues.size() != 0){
            //    throw new UnsupportedOperationException("I have solved parameters for " + clazz.getCanonicalName() +". Values given are: "+typeParameterValues);
            //}
            // if it is zero we are going to ignore them
            if (this.getTypeParameters().size() != 0) {
                // Parameters not specified, so default to Object
                typeParameterValues = new ArrayList<>();
                for (int i = 0; i < getTypeParameters().size(); i++) {
                    typeParameterValues.add(new ReferenceTypeUsage(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver));
                }
            }
        }
        List<MethodUsage> methods = new ArrayList<>();
        for (Method method : clazz.getMethods()) {
            if (method.getName().equals(name) && !method.isBridge() && !method.isSynthetic()) {
                MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
                MethodUsage methodUsage = new MethodUsage(methodDeclaration, typeSolver);
                int i = 0;
                for (TypeParameter tp : getTypeParameters()) {
                    methodUsage = methodUsage.replaceNameParam(tp.getName(), typeParameterValues.get(i));
                    i++;
                }
                methods.add(methodUsage);
            }

        }
        final List<TypeUsage> finalTypeParameterValues = typeParameterValues;
        parameterTypes = parameterTypes.stream().map((pt) -> {
            int i = 0;
            for (TypeParameter tp : getTypeParameters()) {
                pt = pt.replaceParam(tp.getName(), finalTypeParameterValues.get(i));
                i++;
            }
            return pt;
        }).collect(Collectors.toList());
        return MethodResolutionLogic.findMostApplicableUsage(methods, name, parameterTypes, typeSolver);
    }

    @Override
    public boolean canBeAssignedTo(TypeDeclaration other) {
        if (other instanceof LambdaArgumentTypeUsagePlaceholder) {
            return getQualifiedName().equals(Predicate.class.getCanonicalName()) ||
                    getQualifiedName().equals(Function.class.getCanonicalName());
        }
        if (other.getQualifiedName().equals(getQualifiedName())) {
            return true;
        }
        if (this.clazz.getSuperclass() != null) {
            if (new ReflectionInterfaceDeclaration(clazz.getSuperclass(), typeSolver).canBeAssignedTo(other)) {
                return true;
            }
        }
        for (Class interfaze : clazz.getInterfaces()) {
            if (new ReflectionInterfaceDeclaration(interfaze, typeSolver).canBeAssignedTo(other)) {
                return true;
            }
        }

        if (other.getQualifiedName().equals(Object.class.getCanonicalName())) {
            return true;
        }

        return false;
    }

    @Override
    public boolean isAssignableBy(TypeUsage typeUsage) {
        if (typeUsage instanceof NullTypeUsage) {
            return true;
        }
        if (typeUsage instanceof LambdaArgumentTypeUsagePlaceholder) {
            return getQualifiedName().equals(Predicate.class.getCanonicalName()) ||
                    getQualifiedName().equals(Function.class.getCanonicalName());
        }
        if (typeUsage.isArray()) {
            return false;
        }
        if (typeUsage.isPrimitive()) {
            return false;
        }
        if (typeUsage.describe().equals(getQualifiedName())) {
            return true;
        }
        if (typeUsage instanceof ReferenceTypeUsage) {
            ReferenceTypeUsage otherTypeDeclaration = (ReferenceTypeUsage) typeUsage;
            return otherTypeDeclaration.getTypeDeclaration().canBeAssignedTo(this);
        }

        return false;
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }

    @Override
    public FieldDeclaration getField(String name) {
        for (Field field : clazz.getDeclaredFields()) {
            if (field.getName().equals(name)) {
                return new ReflectionFieldDeclaration(field, typeSolver);
            }
        }
        for (ReferenceTypeUsage ancestor : getAllAncestors()) {
            if (ancestor.getTypeDeclaration().hasField(name)) {
                return ancestor.getTypeDeclaration().getField(name);
            }
        }
        throw new UnsolvedSymbolException("Field in " + this, name);
    }

    /*@Override
    public boolean canBeAssignedTo(TypeDeclaration other, TypeSolver typeSolver) {
        if (getQualifiedName().equals(other.getQualifiedName())) {
            return true;
        }
        if (clazz.getSuperclass() != null) {
            if (new ReflectionClassDeclaration(clazz.getSuperclass()).isAssignableBy(other, typeSolver)){
                return true;
            }
        }
        for (Class<?> interfaze : clazz.getInterfaces()) {
            if (new ReflectionClassDeclaration(interfaze).isAssignableBy(other, typeSolver)){
                return true;
            }
        }
        return false;
    }*/

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Field field : clazz.getFields()) {
            if (field.getName().equals(name)) {
                return SymbolReference.solved(new ReflectionFieldDeclaration(field, typeSolver));
            }
        }
        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String substring, TypeSolver typeSolver) {
        return SymbolReference.unsolved(TypeDeclaration.class);
    }

    @Override
    public List<ReferenceTypeUsage> getAllAncestors() {
        List<ReferenceTypeUsage> ancestors = new LinkedList<>();
        if (clazz.getSuperclass() != null) {
            ReferenceTypeUsage superclass = new ReferenceTypeUsage(new ReflectionInterfaceDeclaration(clazz.getSuperclass(), typeSolver), typeSolver);
            ancestors.add(superclass);
            ancestors.addAll(superclass.getAllAncestors());
        }
        for (Class<?> interfaze : clazz.getInterfaces()) {
            ReferenceTypeUsage interfazeDecl = new ReferenceTypeUsage(new ReflectionInterfaceDeclaration(interfaze, typeSolver), typeSolver);
            ancestors.add(interfazeDecl);
            ancestors.addAll(interfazeDecl.getAllAncestors());
        }
        for (int i = 0; i < ancestors.size(); i++) {
            if (ancestors.get(i).getQualifiedName().equals(Object.class.getCanonicalName())) {
                ancestors.remove(i);
                i--;
            }
        }
        ReferenceTypeUsage object = new ReferenceTypeUsage(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        ancestors.add(object);
        return ancestors;
    }

    @Override
    public boolean hasField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return clazz.getSimpleName();
    }

    @Override
    public boolean isInterface() {
        return true;
    }

    @Override
    public List<InterfaceDeclaration> getInterfacesExtended() {
        List<InterfaceDeclaration> res = new ArrayList<>();
        for (Class i : clazz.getInterfaces()) {
            res.add(new ReflectionInterfaceDeclaration(i, typeSolver));
        }
        return res;
    }

    @Override
    public InterfaceDeclaration asInterface() {
        return this;
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        List<TypeParameter> params = new ArrayList<>();
        for (TypeVariable tv : this.clazz.getTypeParameters()) {
            params.add(new ReflectionTypeParameter(tv, true));
        }
        return params;
    }

    @Override
    protected TypeSolver typeSolver() {
        return typeSolver;
    }
}
