package me.tomassetti.symbolsolver.model.javassist;

import javassist.CtClass;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.usages.ArrayTypeUsage;
import me.tomassetti.symbolsolver.model.usages.PrimitiveTypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;

/**
 * Created by federico on 20/08/15.
 */
public class JavassistFactory {

    public static TypeUsage typeUsageFor(CtClass ctClazz) {
        try {
            if (ctClazz.isArray()) {
                return new ArrayTypeUsage(typeUsageFor(ctClazz.getComponentType()));
            } else if (ctClazz.isPrimitive()) {
                return PrimitiveTypeUsage.byName(ctClazz.getName());
            } else {
                return new TypeUsageOfTypeDeclaration(new JavassistClassDeclaration(ctClazz));
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }
}
