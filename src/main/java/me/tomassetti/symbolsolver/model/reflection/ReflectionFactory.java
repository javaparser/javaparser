package me.tomassetti.symbolsolver.model.reflection;

import javassist.CtClass;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.javassist.JavassistClassDeclaration;
import me.tomassetti.symbolsolver.model.usages.*;

/**
 * Created by federico on 02/08/15.
 */
public class ReflectionFactory {
    public static TypeUsage typeUsageFor(Class<?> clazz) {
        if (clazz.isArray()) {
            return new ArrayTypeUsage(typeUsageFor(clazz.getComponentType()));
        } else if (clazz.isPrimitive()) {
            if (clazz.getName().equals("void")) {
                return new VoidTypeUsage();
            } else {
                return PrimitiveTypeUsage.byName(clazz.getName());
            }
        } else if (clazz.isInterface()) {
            return new TypeUsageOfTypeDeclaration(new ReflectionInterfaceDeclaration(clazz));
        } else {
            return new TypeUsageOfTypeDeclaration(new ReflectionClassDeclaration(clazz));
        }
    }
}
