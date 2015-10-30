package me.tomassetti.symbolsolver.resolution.reflection;





import me.tomassetti.symbolsolver.model.typesystem.*;


import java.lang.reflect.GenericArrayType;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.lang.reflect.TypeVariable;

/**
 * Created by federico on 02/08/15.
 */
public class ReflectionFactory {
    public static TypeUsage typeUsageFor(Class<?> clazz) {
        if (clazz.isArray()) {
            return new ArrayTypeUsage(typeUsageFor(clazz.getComponentType()));
        } else if (clazz.isPrimitive()) {
            if (clazz.getName().equals("void")) {
                return VoidTypeUsage.INSTANCE;
            } else {
                return PrimitiveTypeUsage.byName(clazz.getName());
            }
        } else if (clazz.isInterface()) {
            return new ReferenceTypeUsage(new ReflectionInterfaceDeclaration(clazz));
        } else {
            return new ReferenceTypeUsage(new ReflectionClassDeclaration(clazz));
        }
    }

    public static TypeUsage typeUsageFor(Type type) {
        if (type instanceof TypeVariable) {
            TypeVariable tv = (TypeVariable) type;
            // TODO the false value is arbitrary...
            me.tomassetti.symbolsolver.resolution.TypeParameter typeParameter = new ReflectionTypeParameter(tv, true);
            return new TypeUsageOfTypeParameter(typeParameter);
        } else if (type instanceof ParameterizedType) {
            ParameterizedType pt = (ParameterizedType) type;
            // TODO deal with type parameters
            return typeUsageFor(pt.getRawType());
        } else if (type instanceof Class) {
            Class c = (Class) type;
            if (c.isPrimitive()) {
                if (c.getName().equals("void")) {
                    return VoidTypeUsage.INSTANCE;
                } else {
                    return PrimitiveTypeUsage.byName(c.getName());
                }
            } else if (c.isArray()) {
                return new ArrayTypeUsage(typeUsageFor(c.getComponentType()));
            } else if (c.isInterface()) {
                return new ReferenceTypeUsage(new ReflectionInterfaceDeclaration(c));
            } else {
                return new ReferenceTypeUsage(new ReflectionClassDeclaration(c));
            }
        } else if (type instanceof GenericArrayType){
            GenericArrayType genericArrayType = (GenericArrayType)type;
            return new ArrayTypeUsage(typeUsageFor(genericArrayType.getGenericComponentType()));
        } else {
            throw new UnsupportedOperationException(type.getClass().getCanonicalName()+" "+type);
        }
    }
}
