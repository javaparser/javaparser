/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.Node;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.LambdaArgumentTypePlaceholder;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ContextHelper;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.*;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.model.methods.MethodUsage;
import com.github.javaparser.symbolsolver.model.typesystem.NullType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;

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
                .map(m -> new ReflectionMethodDeclaration(m, typeSolver))
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
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> argumentsTypes) {
        List<MethodDeclaration> methods = new ArrayList<>();
        for (Method method : Arrays.stream(clazz.getDeclaredMethods()).filter((m) -> m.getName().equals(name)).sorted(new MethodComparator()).collect(Collectors.toList())) {
            if (method.isBridge() || method.isSynthetic()) continue;
            MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            methods.add(methodDeclaration);
        }
        if (getSuperClass() != null) {
            ClassDeclaration superClass = (ClassDeclaration) getSuperClass().getTypeDeclaration();
            SymbolReference<MethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(superClass, name, argumentsTypes, typeSolver);
            if (ref.isSolved()) {
                methods.add(ref.getCorrespondingDeclaration());
            }
        }
        for (ReferenceType interfaceDeclaration : getInterfaces()) {
            SymbolReference<MethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(interfaceDeclaration.getTypeDeclaration(), name, argumentsTypes, typeSolver);
            if (ref.isSolved()) {
                methods.add(ref.getCorrespondingDeclaration());
            }
        }
        return MethodResolutionLogic.findMostApplicable(methods, name, argumentsTypes, typeSolver);
    }

    @Override
    public String toString() {
        return "ReflectionClassDeclaration{" +
                "clazz=" + getId() +
                '}';
    }

    public Type getUsage(Node node) {

        return new ReferenceTypeImpl(this, typeSolver);
    }

    public Optional<MethodUsage> solveMethodAsUsage(String name, List<Type> argumentsTypes, TypeSolver typeSolver, Context invokationContext, List<Type> typeParameterValues) {
        List<MethodUsage> methods = new ArrayList<>();
        for (Method method : Arrays.stream(clazz.getDeclaredMethods()).filter((m) -> m.getName().equals(name)).sorted(new MethodComparator()).collect(Collectors.toList())) {
            if (method.isBridge() || method.isSynthetic()) continue;
            MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            MethodUsage methodUsage = new MethodUsage(methodDeclaration);
            for (int i = 0; i < getTypeParameters().size(); i++) {
                TypeParameterDeclaration tpToReplace = getTypeParameters().get(i);
                Type newValue = typeParameterValues.get(i);
                methodUsage = methodUsage.replaceTypeParameter(tpToReplace, newValue);
            }
            methods.add(methodUsage);
        }
        if (getSuperClass() != null) {
            ClassDeclaration superClass = (ClassDeclaration) getSuperClass().getTypeDeclaration();
            Optional<MethodUsage> ref = ContextHelper.solveMethodAsUsage(superClass, name, argumentsTypes, typeSolver, invokationContext, typeParameterValues);
            if (ref.isPresent()) {
                methods.add(ref.get());
            }
        }
        for (ReferenceType interfaceDeclaration : getInterfaces()) {
            Optional<MethodUsage> ref = ContextHelper.solveMethodAsUsage(interfaceDeclaration.getTypeDeclaration(), name, argumentsTypes, typeSolver, invokationContext, typeParameterValues);
            if (ref.isPresent()) {
                methods.add(ref.get());
            }
        }
        Optional<MethodUsage> ref = MethodResolutionLogic.findMostApplicableUsage(methods, name, argumentsTypes, typeSolver);
        return ref;
    }

    @Override
    public boolean canBeAssignedTo(TypeDeclaration other) {
        if (other instanceof LambdaArgumentTypePlaceholder) {
            // FIXME remove and use functional interface recognition
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
    public boolean isTypeParameter() {
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
                ReflectionFieldDeclaration reflectionFieldDeclaration = (ReflectionFieldDeclaration) ancestor.getTypeDeclaration().getField(name);
                return reflectionFieldDeclaration.replaceType(ancestor.getFieldType(name).get());
            }
        }
        throw new UnsolvedSymbolException(name, "Field in " + this);
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
        for (java.lang.reflect.Type superInterface : clazz.getGenericInterfaces()) {
            if (superInterface instanceof ParameterizedType) {
                ParameterizedType parameterizedType = (ParameterizedType) superInterface;
                List<Type> typeParameters = Arrays.stream(parameterizedType.getActualTypeArguments())
                        .map((t) -> ReflectionFactory.typeUsageFor(t, typeSolver))
                        .collect(Collectors.toList());
                interfaces.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration((Class)((ParameterizedType) superInterface).getRawType(), typeSolver), typeParameters, typeSolver));
            } else {
                interfaces.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration((Class)superInterface, typeSolver), typeSolver));
            }
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
            params.add(new ReflectionTypeParameter(tv, true, typeSolver));
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
