package me.tomassetti.symbolsolver.model.reflection;

import com.github.javaparser.ast.Node;

import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.model.usages.*;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.TypeVariable;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Created by federico on 02/08/15.
 */
public class ReflectionInterfaceDeclaration implements InterfaceDeclaration {

    private Class<?> clazz;

    public ReflectionInterfaceDeclaration(Class<?> clazz) {
        if (!clazz.isInterface()) {
            throw new IllegalArgumentException();
        }

        this.clazz = clazz;
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
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        List<MethodDeclaration> methods = new ArrayList<>();
        for (Method method : clazz.getMethods()) {
            if (method.isBridge() || method.isSynthetic()) continue;
            MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method);
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

    @Override
    public TypeUsage getUsage(Node node) {
        
        return new TypeUsageOfTypeDeclaration(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ReflectionInterfaceDeclaration that = (ReflectionInterfaceDeclaration) o;

        if (!clazz.equals(that.clazz)) return false;

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
                    typeParameterValues.add(new TypeUsageOfTypeDeclaration(new ReflectionClassDeclaration(Object.class)));
                }
            }
        }
        List<MethodUsage> methods = new ArrayList<>();
        for (Method method : clazz.getMethods()) {
            if (method.getName().equals(name) && !method.isBridge() && !method.isSynthetic()) {
                MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method);
                MethodUsage methodUsage = new MethodUsage(methodDeclaration, typeSolver);
                int i = 0;
                for (TypeParameter tp : getTypeParameters()) {
                    methodUsage = methodUsage.replaceNameParam(tp.getName(), typeParameterValues.get(i));
                    i++;
                }
                methods.add(methodUsage);
            }

        }
        return MethodResolutionLogic.findMostApplicableUsage(methods, name, parameterTypes, typeSolver);
    }

    @Override
    public boolean canBeAssignedTo(TypeDeclaration other, TypeSolver typeSolver) {
        if (other instanceof LambdaTypeUsagePlaceholder) {
            return getQualifiedName().equals(Predicate.class.getCanonicalName()) ||
                    getQualifiedName().equals(Function.class.getCanonicalName());
        }
        if (other.getQualifiedName().equals(getQualifiedName())){
            return true;
        }
        if (this.clazz.getSuperclass() != null) {
            if (new ReflectionInterfaceDeclaration(clazz.getSuperclass()).canBeAssignedTo(other, typeSolver)){
                return true;
            }
        }
        for (Class interfaze : clazz.getInterfaces()){
            if (new ReflectionInterfaceDeclaration(interfaze).canBeAssignedTo(other, typeSolver)){
                return true;
            }
        }

        if (other.getQualifiedName().equals(Object.class.getCanonicalName())) {
            return true;
        }

        return false;
    }

    @Override
    public boolean isAssignableBy(TypeUsage typeUsage, TypeSolver typeSolver) {
        if (typeUsage instanceof NullTypeUsage) {
            return true;
        }
        if (typeUsage instanceof LambdaTypeUsagePlaceholder) {
            return getQualifiedName().equals(Predicate.class.getCanonicalName()) ||
                    getQualifiedName().equals(Function.class.getCanonicalName());
        }
        if (typeUsage.isArray()) {
            return false;
        }
        if (typeUsage.isPrimitive()){
            return false;
        }
        if (typeUsage.getTypeName().equals(getQualifiedName())){
            return true;
        }
        if (typeUsage instanceof TypeUsageOfTypeDeclaration){
            TypeUsageOfTypeDeclaration otherTypeDeclaration = (TypeUsageOfTypeDeclaration)typeUsage;
            return otherTypeDeclaration.getTypeDeclaration().canBeAssignedTo(this, typeSolver);
        }

        return false;
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }

    @Override
    public FieldDeclaration getField(String name, TypeSolver typeSolver) {
        for (Field field : clazz.getDeclaredFields()) {
            if (field.getName().equals(name)) {
                return new ReflectionFieldDeclaration(field);
            }
        }
        for (TypeUsageOfTypeDeclaration ancestor : getAllAncestors(typeSolver)) {
            if (ancestor.getTypeDeclaration().hasField(name, typeSolver)) {
                return ancestor.getTypeDeclaration().getField(name, typeSolver);
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
        for (Field field : clazz.getFields()){
            if (field.getName().equals(name)) {
                return SymbolReference.solved(new ReflectionFieldDeclaration(field));
            }
        }
        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String substring, TypeSolver typeSolver) {
        return SymbolReference.unsolved(TypeDeclaration.class);
    }

    @Override
    public List<TypeUsageOfTypeDeclaration> getAllAncestors(TypeSolver typeSolver) {
        List<TypeUsageOfTypeDeclaration> ancestors = new LinkedList<>();
        if (clazz.getSuperclass() != null) {
            TypeUsageOfTypeDeclaration superclass = new TypeUsageOfTypeDeclaration(new ReflectionInterfaceDeclaration(clazz.getSuperclass()));
            ancestors.add(superclass);
            ancestors.addAll(superclass.getAllAncestors(typeSolver));
        }
        for (Class<?> interfaze : clazz.getInterfaces()) {
            TypeUsageOfTypeDeclaration interfazeDecl = new TypeUsageOfTypeDeclaration(new ReflectionInterfaceDeclaration(interfaze));
            ancestors.add(interfazeDecl);
            ancestors.addAll(interfazeDecl.getAllAncestors(typeSolver));
        }
        return ancestors;
    }

    @Override
    public boolean hasField(String name, TypeSolver typeSolver) {
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
    public List<InterfaceDeclaration> getInterfacesExtended(TypeSolver typeSolver) {
        List<InterfaceDeclaration> res = new ArrayList<>();
        for (Class i : clazz.getInterfaces()) {
            res.add(new ReflectionInterfaceDeclaration(i));
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
}
