package me.tomassetti.symbolsolver.javassistmodel;

import javassist.CtClass;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
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
                if (ctClazz.isInterface()) {
                    return new ReferenceTypeUsageImpl(new JavassistInterfaceDeclaration(ctClazz, typeSolver), typeSolver);
                } else {
                    return new ReferenceTypeUsageImpl(new JavassistClassDeclaration(ctClazz, typeSolver), typeSolver);
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    public static TypeDeclaration toTypeDeclaration(CtClass ctClazz, TypeSolver typeSolver) {
        if (ctClazz.isInterface()) {
            return new JavassistInterfaceDeclaration(ctClazz, typeSolver);
        } else if (ctClazz.isEnum()) {
            throw new UnsupportedOperationException("CtClass of enum not yet supported");
        } else if (ctClazz.isAnnotation()) {
            throw new UnsupportedOperationException("CtClass of annotation not yet supported");
        } else if (ctClazz.isArray()) {
            throw new IllegalArgumentException("This method should not be called passing an array");
        } else {
            return new JavassistClassDeclaration(ctClazz, typeSolver);
        }
    }
}
