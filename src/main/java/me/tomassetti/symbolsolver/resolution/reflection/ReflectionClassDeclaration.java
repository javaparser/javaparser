package me.tomassetti.symbolsolver.resolution.reflection;

import com.github.javaparser.ast.Node;

import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.resolution.*;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.resolution.javaparser.LambdaArgumentTypeUsagePlaceholder;
import me.tomassetti.symbolsolver.resolution.javaparser.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.model.typesystem.*;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Parameter;
import java.lang.reflect.TypeVariable;
import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;

import java.util.stream.Collectors;

public class ReflectionClassDeclaration implements ClassDeclaration {

    private Class<?> clazz;
    private TypeSolver typeSolver;

    @Override
    public List<ReferenceTypeUsage> getAllAncestors() {
        List<ReferenceTypeUsage> ancestors = new LinkedList<>();
        if (getSuperClass(typeSolver) != null) {
            ancestors.add(new ReferenceTypeUsage(getSuperClass(typeSolver), typeSolver));
            ancestors.addAll(getSuperClass(typeSolver).getAllAncestors());
        }
        ancestors.addAll(getAllInterfaces(typeSolver).stream().map((i)->new ReferenceTypeUsage(i, typeSolver)).collect(Collectors.<ReferenceTypeUsage>toList()));
        return ancestors;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ReflectionClassDeclaration that = (ReflectionClassDeclaration) o;

        if (!clazz.getCanonicalName().equals(that.clazz.getCanonicalName())) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return clazz.hashCode();
    }

    public ReflectionClassDeclaration(Class<?> clazz, TypeSolver typeSolver) {
        this.typeSolver = typeSolver;
        if (clazz.isInterface()) {
            throw new IllegalArgumentException();
        }
        if (clazz.isPrimitive()) {
            throw new IllegalArgumentException();
        }
        if (clazz.isArray()) {
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

    private static class ParameterComparator implements Comparator<Parameter> {

        @Override
        public int compare(Parameter o1, Parameter o2) {
            int compareName = o1.getName().compareTo(o2.getName());
            if (compareName != 0) return compareName;
            int compareType = new ClassComparator().compare(o1.getType(), o2.getType());
            if (compareType != 0) return compareType;
            return 0;
        }
    }

    private static class ClassComparator implements Comparator<Class<?>> {

        @Override
        public int compare(Class<?> o1, Class<?> o2) {
            int subCompare;
            subCompare = o1.getCanonicalName().compareTo(o2.getCanonicalName());
            if (subCompare != 0) return subCompare;
            subCompare = Boolean.compare(o1.isAnnotation(), o2.isAnnotation());
            if (subCompare != 0) return subCompare;
            subCompare = Boolean.compare(o1.isArray(), o2.isArray());
            if (subCompare != 0) return subCompare;
            subCompare = Boolean.compare(o1.isEnum(), o2.isEnum());
            if (subCompare != 0) return subCompare;
            subCompare = Boolean.compare(o1.isInterface(), o2.isInterface());
            if (subCompare != 0) return subCompare;
            return 0;
        }
    }

    private static class MethodComparator implements Comparator<Method> {

        @Override
        public int compare(Method o1, Method o2) {
            int compareName = o1.getName().compareTo(o2.getName());
            if (compareName != 0) return compareName;
            int compareNParams = o1.getParameterCount() - o2.getParameterCount();
            if (compareNParams != 0) return compareNParams;
            for (int i=0;i<o1.getParameterCount();i++) {
                int compareParam = new ParameterComparator().compare(o1.getParameters()[i], o2.getParameters()[i]);
                if (compareParam != 0) return compareParam;
            }
            int compareResult = new ClassComparator().compare(o1.getReturnType(), o2.getReturnType());
            if (compareResult != 0) return compareResult;
            return 0;
        }
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        List<MethodDeclaration> methods = new ArrayList<>();
        for (Method method : Arrays.stream(clazz.getDeclaredMethods()).filter((m) -> m.getName().equals(name)).sorted(new MethodComparator()).collect(Collectors.toList())) {
            if (method.isBridge() || method.isSynthetic()) continue;
            MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            methods.add(methodDeclaration);
        }
        ClassDeclaration superClass = getSuperClass(typeSolver);
        if (superClass != null) {
            SymbolReference<MethodDeclaration> ref = superClass.solveMethod(name, parameterTypes, typeSolver);
            if (ref.isSolved()) {
                methods.add(ref.getCorrespondingDeclaration());
            }
        }
        for (InterfaceDeclaration interfaceDeclaration : getInterfaces(typeSolver)) {
            SymbolReference<MethodDeclaration> ref = interfaceDeclaration.solveMethod(name, parameterTypes, typeSolver);
            if (ref.isSolved()) {
                methods.add(ref.getCorrespondingDeclaration());
            }
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
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext, List<TypeUsage> typeParameterValues) {
        List<MethodUsage> methods = new ArrayList<>();
        for (Method method : Arrays.stream(clazz.getDeclaredMethods()).filter((m) -> m.getName().equals(name)).sorted(new MethodComparator()).collect(Collectors.toList())) {
            if (method.isBridge() || method.isSynthetic()) continue;
            MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            MethodUsage methodUsage = new MethodUsage(methodDeclaration, typeSolver);
            for (int i=0;i<getTypeParameters().size();i++){
                String nameToReplace = getTypeParameters().get(i).getName();
                TypeUsage newValue = typeParameterValues.get(i);
                methodUsage = methodUsage.replaceNameParam(nameToReplace, newValue);
            }
            methods.add(methodUsage);
        }
        ClassDeclaration superClass = getSuperClass(typeSolver);
        if (superClass != null) {
            Optional<MethodUsage> ref = superClass.solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext, typeParameterValues);
            if (ref.isPresent()) {
                methods.add(ref.get());
            }
        }
        for (InterfaceDeclaration interfaceDeclaration : getInterfaces(typeSolver)) {
            Optional<MethodUsage> ref = interfaceDeclaration.solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext, typeParameterValues);
            if (ref.isPresent()) {
                methods.add(ref.get());
            }
        }
        Optional<MethodUsage> ref = MethodResolutionLogic.findMostApplicableUsage(methods, name, parameterTypes, typeSolver);
        return ref;
    }

    @Override
    public boolean canBeAssignedTo(TypeDeclaration other) {
        if (other instanceof LambdaArgumentTypeUsagePlaceholder) {
            return getQualifiedName().equals(Predicate.class.getCanonicalName()) ||
                    getQualifiedName().equals(Function.class.getCanonicalName());
        }
        if (other.getQualifiedName().equals(getQualifiedName())){
            return true;
        }
        if (this.clazz.getSuperclass() != null) {
            if (new ReflectionClassDeclaration(clazz.getSuperclass(), typeSolver).canBeAssignedTo(other)){
                return true;
            }
        }
        for (Class interfaze : clazz.getInterfaces()){
            if (new ReflectionInterfaceDeclaration(interfaze, typeSolver).canBeAssignedTo(other)){
                return true;
            }
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
        if (typeUsage.isPrimitive()){
            return false;
        }
        if (typeUsage.describe().equals(getQualifiedName())){
            return true;
        }
        if (typeUsage instanceof ReferenceTypeUsage){
            ReferenceTypeUsage otherTypeDeclaration = (ReferenceTypeUsage)typeUsage;
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
                return new ReflectionFieldDeclaration(field);
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
    public ClassDeclaration asClass() {
        return this;
    }

    @Override
    public boolean hasField(String name) {
        for (Field field : clazz.getDeclaredFields()){
            if (field.getName().equals(name)) {
                return true;
            }
        }
        ClassDeclaration superclass = getSuperClass(typeSolver);
        if (superclass == null) {
            return false;
        } else {
            return superclass.hasField(name);
        }
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeUsage(other, typeSolver));
    }

    @Override
    public String getName() {
        return clazz.getSimpleName();
    }

    @Override
    public boolean isField() {
        return false;
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
        return true;
    }

    @Override
    public boolean isClass() {
        return !clazz.isInterface();
    }

    @Override
    public ClassDeclaration getSuperClass(TypeSolver typeSolvers) {
        if (clazz.getSuperclass() == null) {
            return null;
        }
        return new ReflectionClassDeclaration(clazz.getSuperclass(), typeSolver);
    }

    @Override
    public List<InterfaceDeclaration> getInterfaces(TypeSolver typeSolver) {
        List<InterfaceDeclaration> interfaces = new ArrayList<>();
        for (Class i : clazz.getInterfaces()) {
            interfaces.add(new ReflectionInterfaceDeclaration(i, typeSolver));
        }
        return interfaces;
    }

    @Override
    public boolean isInterface() {
        return clazz.isInterface();
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
