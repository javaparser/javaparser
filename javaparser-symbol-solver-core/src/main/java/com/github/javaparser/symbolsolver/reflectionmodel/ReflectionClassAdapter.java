package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.LambdaArgumentTypePlaceholder;
import com.github.javaparser.symbolsolver.logic.FunctionalInterfaceLogic;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.NullType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;

import java.lang.annotation.Annotation;
import java.lang.reflect.Field;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.TypeVariable;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
class ReflectionClassAdapter {

    private Class<?> clazz;
    private TypeSolver typeSolver;
    private ResolvedReferenceTypeDeclaration typeDeclaration;

    public ReflectionClassAdapter(Class<?> clazz, TypeSolver typeSolver, ResolvedReferenceTypeDeclaration typeDeclaration) {
        this.clazz = clazz;
        this.typeSolver = typeSolver;
        this.typeDeclaration = typeDeclaration;
    }

    public ReferenceTypeImpl getSuperClass() {
        if (clazz.getGenericSuperclass() == null) {
            return null;
        }
        java.lang.reflect.Type superType = clazz.getGenericSuperclass();
        if (superType instanceof ParameterizedType) {
            ParameterizedType parameterizedType = (ParameterizedType) superType;
            List<ResolvedType> typeParameters = Arrays.stream(parameterizedType.getActualTypeArguments())
                    .map((t) -> ReflectionFactory.typeUsageFor(t, typeSolver))
                    .collect(Collectors.toList());
            return new ReferenceTypeImpl(new ReflectionClassDeclaration(clazz.getSuperclass(), typeSolver), typeParameters, typeSolver);
        }
        return new ReferenceTypeImpl(new ReflectionClassDeclaration(clazz.getSuperclass(), typeSolver), typeSolver);
    }

    public List<ResolvedReferenceType> getInterfaces() {
        List<ResolvedReferenceType> interfaces = new ArrayList<>();
        for (java.lang.reflect.Type superInterface : clazz.getGenericInterfaces()) {
            if (superInterface instanceof ParameterizedType) {
                ParameterizedType parameterizedType = (ParameterizedType) superInterface;
                List<ResolvedType> typeParameters = Arrays.stream(parameterizedType.getActualTypeArguments())
                        .map((t) -> ReflectionFactory.typeUsageFor(t, typeSolver))
                        .collect(Collectors.toList());
                interfaces.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration((Class<?>) ((ParameterizedType) superInterface).getRawType(), typeSolver), typeParameters, typeSolver));
            } else {
                interfaces.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration((Class<?>) superInterface, typeSolver), typeSolver));
            }
        }
        return interfaces;
    }

    public List<ResolvedReferenceType> getAncestors() {
        List<ResolvedReferenceType> ancestors = new LinkedList<>();
        if (getSuperClass() != null) {
            ReferenceTypeImpl superClass = getSuperClass();
            ancestors.add(superClass);
        } else {
            ReferenceTypeImpl object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
            ancestors.add(object);
        }
        ancestors.addAll(getInterfaces());
        for (int i = 0; i < ancestors.size(); i++) {
            ResolvedReferenceType ancestor = ancestors.get(i);
            if (ancestor.hasName() && ancestor.getQualifiedName().equals(Object.class.getCanonicalName())) {
                ancestors.remove(i);
                i--;
            }
        }
        return ancestors;
    }

    public ResolvedFieldDeclaration getField(String name) {
        for (Field field : clazz.getDeclaredFields()) {
            if (field.getName().equals(name)) {
                return new ReflectionFieldDeclaration(field, typeSolver);
            }
        }
        for (ResolvedReferenceType ancestor : typeDeclaration.getAllAncestors()) {
            if (ancestor.getTypeDeclaration().hasField(name)) {
                ReflectionFieldDeclaration reflectionFieldDeclaration = (ReflectionFieldDeclaration) ancestor.getTypeDeclaration().getField(name);
                return reflectionFieldDeclaration.replaceType(ancestor.getFieldType(name).get());
            }
        }
        throw new UnsolvedSymbolException(name, "Field in " + this);
    }

    public boolean hasField(String name) {
        for (Field field : clazz.getDeclaredFields()) {
            if (field.getName().equals(name)) {
                return true;
            }
        }
        for (ResolvedReferenceType ancestor : typeDeclaration.getAllAncestors()) {
            if (ancestor.getTypeDeclaration().hasField(name)) {
                return true;
            }
        }
        return false;
    }

    public List<ResolvedFieldDeclaration> getAllFields() {
        ArrayList<ResolvedFieldDeclaration> fields = new ArrayList<>();
        for (Field field : clazz.getDeclaredFields()) {
            fields.add(new ReflectionFieldDeclaration(field, typeSolver));
        }
        for (ResolvedReferenceType ancestor : typeDeclaration.getAllAncestors()) {
            fields.addAll(ancestor.getTypeDeclaration().getAllFields());
        }
        return fields;
    }

    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        return Arrays.stream(clazz.getDeclaredMethods())
                .filter(m -> !m.isSynthetic() && !m.isBridge())
                .map(m -> new ReflectionMethodDeclaration(m, typeSolver))
                .collect(Collectors.toSet());
    }

    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        List<ResolvedTypeParameterDeclaration> params = new ArrayList<>();
        for (TypeVariable<?> tv : this.clazz.getTypeParameters()) {
            params.add(new ReflectionTypeParameter(tv, true, typeSolver));
        }
        return params;
    }

    public boolean isAssignableBy(ResolvedType type) {
        if (type instanceof NullType) {
            return true;
        }
        if (type instanceof LambdaArgumentTypePlaceholder) {
            return isFunctionalInterface();
        }
        if (type.isArray()) {
            return false;
        }
        if (type.isPrimitive()) {
            return false;
        }
        if (type.describe().equals(typeDeclaration.getQualifiedName())) {
            return true;
        }
        if (type instanceof ReferenceTypeImpl) {
            ReferenceTypeImpl otherTypeDeclaration = (ReferenceTypeImpl) type;
            return otherTypeDeclaration.getTypeDeclaration().canBeAssignedTo(typeDeclaration);
        }

        return false;
    }

    public boolean hasDirectlyAnnotation(String canonicalName) {
        for (Annotation a : clazz.getDeclaredAnnotations()) {
            if (a.annotationType().getCanonicalName().equals(canonicalName)) {
                return true;
            }
        }
        return false;
    }

    private final boolean isFunctionalInterface() {
        return FunctionalInterfaceLogic.getFunctionalMethod(typeDeclaration).isPresent();
    }

    public List<ResolvedConstructorDeclaration> getConstructors() {
        return Arrays.stream(clazz.getDeclaredConstructors())
                .filter(m -> !m.isSynthetic())
                .map(m -> new ReflectionConstructorDeclaration(m, typeSolver))
                .collect(Collectors.toList());
    }
    
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        Class<?> declaringClass = clazz.getDeclaringClass();
        return declaringClass == null ?
                Optional.empty() :
                Optional.of(ReflectionFactory.typeDeclarationFor(declaringClass, typeSolver));
    }
}
