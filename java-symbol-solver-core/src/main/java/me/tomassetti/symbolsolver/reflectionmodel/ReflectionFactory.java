package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.*;

import java.lang.reflect.*;

public class ReflectionFactory {
    public static TypeUsage typeUsageFor(Class<?> clazz, TypeSolver typeSolver) {
        if (clazz.isArray()) {
            return new ArrayTypeUsage(typeUsageFor(clazz.getComponentType(), typeSolver));
        } else if (clazz.isPrimitive()) {
            if (clazz.getName().equals("void")) {
                return VoidTypeUsage.INSTANCE;
            } else {
                return PrimitiveTypeUsage.byName(clazz.getName());
            }
        } else if (clazz.isInterface()) {
            return new ReferenceTypeUsageImpl(new ReflectionInterfaceDeclaration(clazz, typeSolver), typeSolver);
        } else {
            return new ReferenceTypeUsageImpl(new ReflectionClassDeclaration(clazz, typeSolver), typeSolver);
        }
    }

    public static TypeUsage typeUsageFor(Type type, TypeSolver typeSolver) {
        if (type instanceof TypeVariable) {
            TypeVariable tv = (TypeVariable) type;
            // TODO the false value is arbitrary...
            me.tomassetti.symbolsolver.model.resolution.TypeParameter typeParameter = new ReflectionTypeParameter(tv, true);
            return new TypeParameterUsage(typeParameter);
        } else if (type instanceof ParameterizedType) {
            ParameterizedType pt = (ParameterizedType) type;
            ReferenceTypeUsage rawType = typeUsageFor(pt.getRawType(), typeSolver).asReferenceTypeUsage();
            int i = 0;
            for (Type actualTypeArgument : pt.getActualTypeArguments()) {
                rawType = rawType.replaceParam(i, typeUsageFor(actualTypeArgument, typeSolver)).asReferenceTypeUsage();
                i++;
            }
            return rawType;
        } else if (type instanceof Class) {
            Class c = (Class) type;
            if (c.isPrimitive()) {
                if (c.getName().equals("void")) {
                    return VoidTypeUsage.INSTANCE;
                } else {
                    return PrimitiveTypeUsage.byName(c.getName());
                }
            } else if (c.isArray()) {
                return new ArrayTypeUsage(typeUsageFor(c.getComponentType(), typeSolver));
            } else if (c.isInterface()) {
                return new ReferenceTypeUsageImpl(new ReflectionInterfaceDeclaration(c, typeSolver), typeSolver);
            } else {
                return new ReferenceTypeUsageImpl(new ReflectionClassDeclaration(c, typeSolver), typeSolver);
            }
        } else if (type instanceof GenericArrayType) {
            GenericArrayType genericArrayType = (GenericArrayType) type;
            return new ArrayTypeUsage(typeUsageFor(genericArrayType.getGenericComponentType(), typeSolver));
        } else if (type instanceof WildcardType) {
            WildcardType wildcardType = (WildcardType) type;
            if (wildcardType.getLowerBounds().length > 0 && wildcardType.getUpperBounds().length > 0) {
                if (wildcardType.getUpperBounds().length == 1 && wildcardType.getUpperBounds()[0].getTypeName().equals("java.lang.Object")) {
                    // ok, it does not matter
                }
            }
            if (wildcardType.getLowerBounds().length > 0) {
                if (wildcardType.getLowerBounds().length > 1) {
                    throw new UnsupportedOperationException();
                }
                return WildcardUsage.superBound(typeUsageFor(wildcardType.getLowerBounds()[0], typeSolver));
            }
            if (wildcardType.getUpperBounds().length > 0) {
                if (wildcardType.getUpperBounds().length > 1) {
                    throw new UnsupportedOperationException();
                }
                return WildcardUsage.extendsBound(typeUsageFor(wildcardType.getUpperBounds()[0], typeSolver));
            }
            return WildcardUsage.UNBOUNDED;
        } else {
            throw new UnsupportedOperationException(type.getClass().getCanonicalName() + " " + type);
        }
    }
}
