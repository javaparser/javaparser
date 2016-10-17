package me.tomassetti.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.javaparsermodel.LambdaArgumentTypePlaceholder;
import me.tomassetti.symbolsolver.logic.AbstractClassDeclaration;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.typesystem.NullType;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceTypeImpl;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.resolution.MethodResolutionLogic;

import java.lang.reflect.*;
import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class ReflectionClassDeclaration extends AbstractClassDeclaration {

    private Class<?> clazz;
    private TypeSolver typeSolver;

    @Override
    protected ReferenceType object() {
        return new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver);
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        return Arrays.stream(clazz.getDeclaredMethods())
                .filter(m -> !m.isSynthetic() && !m.isBridge())
                .map(m -> new ReflectionMethodDeclaration(m, typeSolver()))
                .collect(Collectors.toSet());
    }

    public ReflectionClassDeclaration(Class<?> clazz, TypeSolver typeSolver) {
        if (clazz == null) {
            throw new IllegalArgumentException();
        }
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
    protected TypeSolver typeSolver() {
        return typeSolver;
    }

    @Override
    public List<ReferenceType> getAncestors() {
        List<ReferenceType> ancestors = new LinkedList<>();
        if (getSuperClass() != null) {
            ReferenceTypeImpl superClass = getSuperClass();
            ancestors.add(superClass);
        } else {
            ReferenceTypeImpl object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
            ancestors.add(object);
        }
        ancestors.addAll(getInterfaces());
        for (int i = 0; i < ancestors.size(); i++) {
            ReferenceType ancestor = ancestors.get(i);
            if (ancestor.hasName() && ancestor.getQualifiedName().equals(Object.class.getCanonicalName())) {
                ancestors.remove(i);
                i--;
            }
        }
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

    @Override
    public String getQualifiedName() {
        return clazz.getCanonicalName();
    }

    public Context getContext() {
        return new ClassOrInterfaceDeclarationContext(clazz);
    }

    @Deprecated
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes) {
        List<MethodDeclaration> methods = new ArrayList<>();
        for (Method method : Arrays.stream(clazz.getDeclaredMethods()).filter((m) -> m.getName().equals(name)).sorted(new MethodComparator()).collect(Collectors.toList())) {
            if (method.isBridge() || method.isSynthetic()) continue;
            MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            methods.add(methodDeclaration);
        }
        if (getSuperClass() != null) {
            ClassDeclaration superClass = (ClassDeclaration) getSuperClass().getTypeDeclaration();
            SymbolReference<MethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(superClass, name, parameterTypes, typeSolver);
            if (ref.isSolved()) {
                methods.add(ref.getCorrespondingDeclaration());
            }
        }
        for (ReferenceType interfaceDeclaration : getInterfaces()) {
            SymbolReference<MethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(interfaceDeclaration.getTypeDeclaration(), name, parameterTypes, typeSolver);
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

    public Type getUsage(Node node) {

        return new ReferenceTypeImpl(this, typeSolver);
    }

    public Optional<MethodUsage> solveMethodAsUsage(String name, List<Type> parameterTypes, TypeSolver typeSolver, Context invokationContext, List<Type> typeParameterValues) {
        List<MethodUsage> methods = new ArrayList<>();
        for (Method method : Arrays.stream(clazz.getDeclaredMethods()).filter((m) -> m.getName().equals(name)).sorted(new MethodComparator()).collect(Collectors.toList())) {
            if (method.isBridge() || method.isSynthetic()) continue;
            MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            MethodUsage methodUsage = new MethodUsage(methodDeclaration);
            for (int i = 0; i < getTypeParameters().size(); i++) {
                String nameToReplace = getTypeParameters().get(i).getName();
                Type newValue = typeParameterValues.get(i);
                methodUsage = methodUsage.replaceTypeParameterByName(nameToReplace, newValue);
            }
            methods.add(methodUsage);
        }
        if (getSuperClass() != null) {
            ClassDeclaration superClass = (ClassDeclaration) getSuperClass().getTypeDeclaration();
            Optional<MethodUsage> ref = me.tomassetti.symbolsolver.javaparsermodel.contexts.ContextHelper.solveMethodAsUsage(superClass, name, parameterTypes, typeSolver, invokationContext, typeParameterValues);
            if (ref.isPresent()) {
                methods.add(ref.get());
            }
        }
        for (ReferenceType interfaceDeclaration : getInterfaces()) {
            Optional<MethodUsage> ref = me.tomassetti.symbolsolver.javaparsermodel.contexts.ContextHelper.solveMethodAsUsage(interfaceDeclaration.getTypeDeclaration(), name, parameterTypes, typeSolver, invokationContext, typeParameterValues);
            if (ref.isPresent()) {
                methods.add(ref.get());
            }
        }
        Optional<MethodUsage> ref = MethodResolutionLogic.findMostApplicableUsage(methods, name, parameterTypes, typeSolver);
        return ref;
    }

    @Override
    public boolean canBeAssignedTo(TypeDeclaration other) {
        if (other instanceof LambdaArgumentTypePlaceholder) {
            return getQualifiedName().equals(Predicate.class.getCanonicalName()) ||
                    getQualifiedName().equals(Function.class.getCanonicalName());
        }
        if (other.getQualifiedName().equals(getQualifiedName())) {
            return true;
        }
        if (this.clazz.getSuperclass() != null
                && new ReflectionClassDeclaration(clazz.getSuperclass(), typeSolver).canBeAssignedTo(other)) {
                return true;
        }
        for (Class interfaze : clazz.getInterfaces()) {
            if (new ReflectionInterfaceDeclaration(interfaze, typeSolver).canBeAssignedTo(other)) {
                return true;
            }
        }

        return false;
    }

    @Override
    public boolean isAssignableBy(Type type) {
        if (type instanceof NullType) {
            return true;
        }
        if (type instanceof LambdaArgumentTypePlaceholder) {
            return getQualifiedName().equals(Predicate.class.getCanonicalName()) ||
                    getQualifiedName().equals(Function.class.getCanonicalName());
        }
        if (type.isArray()) {
            return false;
        }
        if (type.isPrimitive()) {
            return false;
        }
        if (type.describe().equals(getQualifiedName())) {
            return true;
        }
        if (type instanceof ReferenceTypeImpl) {
            ReferenceTypeImpl otherTypeDeclaration = (ReferenceTypeImpl) type;
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
        for (ReferenceType ancestor : getAllAncestors()) {
            if (ancestor.getTypeDeclaration().hasField(name)) {
                ReflectionFieldDeclaration reflectionFieldDeclaration = (ReflectionFieldDeclaration)ancestor.getTypeDeclaration().getField(name);
                return reflectionFieldDeclaration.replaceType(ancestor.getFieldType(name).get());
            }
        }
        throw new me.tomassetti.symbolsolver.model.resolution.UnsolvedSymbolException("Field in " + this, name);
    }
    
    @Override
    public List<FieldDeclaration> getAllFields() {
        ArrayList<FieldDeclaration> fields = new ArrayList<>();
        for (Field field : clazz.getDeclaredFields()) {
            fields.add(new ReflectionFieldDeclaration(field, typeSolver));
        }
        for (ReferenceType ancestor : getAllAncestors()) {
            fields.addAll(ancestor.getTypeDeclaration().getAllFields());
        }
        return fields;
    }

    @Deprecated
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Field field : clazz.getFields()) {
            if (field.getName().equals(name)) {
                return SymbolReference.solved(new ReflectionFieldDeclaration(field, typeSolver));
            }
        }
        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public ClassDeclaration asClass() {
        return this;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasField(String name) {
        for (Field field : clazz.getDeclaredFields()) {
            if (field.getName().equals(name)) {
                return true;
            }
        }
        ReferenceTypeImpl superclass = getSuperClass();
        if (superclass == null) {
            return false;
        } else {
            return superclass.getTypeDeclaration().hasField(name);
        }
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
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
    public boolean isType() {
        return true;
    }

    @Override
    public boolean isClass() {
        return !clazz.isInterface();
    }

    @Override
    public ReferenceTypeImpl getSuperClass() {
        if (clazz.getGenericSuperclass() == null) {
            return null;
        }
        java.lang.reflect.Type superType = clazz.getGenericSuperclass();
        if (superType instanceof ParameterizedType) {
            ParameterizedType parameterizedType = (ParameterizedType) superType;
            List<Type> typeParameters = Arrays.stream(parameterizedType.getActualTypeArguments())
                    .map((t) -> ReflectionFactory.typeUsageFor(t, typeSolver))
                    .collect(Collectors.toList());
            return new ReferenceTypeImpl(new ReflectionClassDeclaration(clazz.getSuperclass(), typeSolver), typeParameters, typeSolver);
        }
        return new ReferenceTypeImpl(new ReflectionClassDeclaration(clazz.getSuperclass(), typeSolver), typeSolver);
    }

    @Override
    public List<ReferenceType> getInterfaces() {
        List<ReferenceType> interfaces = new ArrayList<>();
        // TODO use genericInterfaces
        for (Class i : clazz.getInterfaces()) {
            interfaces.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(i, typeSolver), typeSolver));
        }
        return interfaces;
    }

    @Override
    public boolean isInterface() {
        return clazz.isInterface();
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        List<TypeParameterDeclaration> params = new ArrayList<>();
        for (TypeVariable tv : this.clazz.getTypeParameters()) {
            params.add(new ReflectionTypeParameter(tv, true));
        }
        return params;
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
            for (int i = 0; i < o1.getParameterCount(); i++) {
                int compareParam = new ParameterComparator().compare(o1.getParameters()[i], o2.getParameters()[i]);
                if (compareParam != 0) return compareParam;
            }
            int compareResult = new ClassComparator().compare(o1.getReturnType(), o2.getReturnType());
            if (compareResult != 0) return compareResult;
            return 0;
        }
    }

    @Override
    public AccessLevel accessLevel() {
        return ReflectionFactory.modifiersToAccessLevel(this.clazz.getModifiers());
    }

    @Override
    public List<ConstructorDeclaration> getConstructors() {
        throw new UnsupportedOperationException();
    }
}
