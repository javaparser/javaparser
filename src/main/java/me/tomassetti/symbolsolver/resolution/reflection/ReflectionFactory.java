package me.tomassetti.symbolsolver.resolution.reflection;

import me.tomassetti.symbolsolver.model.typesystem.*;
import me.tomassetti.symbolsolver.resolution.TypeSolver;

import java.lang.reflect.GenericArrayType;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.lang.reflect.TypeVariable;

/**
 * Created by federico on 02/08/15.
 */
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
            return new ReferenceTypeUsage(new ReflectionInterfaceDeclaration(clazz, typeSolver), typeSolver);
        } else {
            return new ReferenceTypeUsage(new ReflectionClassDeclaration(clazz, typeSolver), typeSolver);
        }
    }

    public static TypeUsage typeUsageFor(Type type, TypeSolver typeSolver) {
        if (type instanceof TypeVariable) {
            TypeVariable tv = (TypeVariable) type;
            // TODO the false value is arbitrary...
            me.tomassetti.symbolsolver.resolution.TypeParameter typeParameter = new ReflectionTypeParameter(tv, true);
            return new TypeParameterUsage(typeParameter);
        } else if (type instanceof ParameterizedType) {
            ParameterizedType pt = (ParameterizedType) type;
            // TODO deal with type parameters
            return typeUsageFor(pt.getRawType(), typeSolver);
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
                return new ReferenceTypeUsage(new ReflectionInterfaceDeclaration(c, typeSolver), typeSolver);
            } else {
                return new ReferenceTypeUsage(new ReflectionClassDeclaration(c, typeSolver), typeSolver);
            }
        } else if (type instanceof GenericArrayType){
            GenericArrayType genericArrayType = (GenericArrayType)type;
            return new ArrayTypeUsage(typeUsageFor(genericArrayType.getGenericComponentType(), typeSolver));
        } else {
            throw new UnsupportedOperationException(type.getClass().getCanonicalName()+" "+type);
        }
    }
}
