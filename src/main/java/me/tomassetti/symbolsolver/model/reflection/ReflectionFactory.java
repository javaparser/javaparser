package me.tomassetti.symbolsolver.model.reflection;

import javassist.CtClass;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.javassist.JavassistClassDeclaration;
import me.tomassetti.symbolsolver.model.usages.ArrayTypeUsage;
import me.tomassetti.symbolsolver.model.usages.PrimitiveTypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;

/**
 * Created by federico on 02/08/15.
 */
public class ReflectionFactory {
    public static TypeUsage typeUsageFor(Class<?> clazz) {
        if (clazz.isArray()) {
            return new ArrayTypeUsage(typeUsageFor(clazz.getComponentType()));
        } else if (clazz.isPrimitive()) {
            return PrimitiveTypeUsage.byName(clazz.getName());
        } else {
            return new TypeUsageOfTypeDeclaration(new ReflectionClassDeclaration(clazz));
        }
    }
}
