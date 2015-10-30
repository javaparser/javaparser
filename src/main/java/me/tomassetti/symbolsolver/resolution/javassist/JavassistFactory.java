package me.tomassetti.symbolsolver.resolution.javassist;

import javassist.CtClass;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.typesystem.ArrayTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.PrimitiveTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;

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
                return new ReferenceTypeUsage(new JavassistClassDeclaration(ctClazz));
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }
}
