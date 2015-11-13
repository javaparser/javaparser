package me.tomassetti.symbolsolver.resolution.javassist;

import javassist.CtClass;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.typesystem.ArrayTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.PrimitiveTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsageImpl;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

public class JavassistFactory {

    public static TypeUsage typeUsageFor(CtClass ctClazz, TypeSolver typeSolver) {
        try {
            if (ctClazz.isArray()) {
                return new ArrayTypeUsage(typeUsageFor(ctClazz.getComponentType(), typeSolver));
            } else if (ctClazz.isPrimitive()) {
                return PrimitiveTypeUsage.byName(ctClazz.getName());
            } else {
                return new ReferenceTypeUsageImpl(new JavassistClassDeclaration(ctClazz, typeSolver), typeSolver);
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }
}
