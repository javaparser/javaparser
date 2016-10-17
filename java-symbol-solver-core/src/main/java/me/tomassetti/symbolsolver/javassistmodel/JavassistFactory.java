package me.tomassetti.symbolsolver.javassistmodel;

import javassist.CtClass;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.typesystem.ArrayType;
import me.tomassetti.symbolsolver.model.usages.typesystem.PrimitiveType;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceTypeImpl;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.model.usages.typesystem.VoidType;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

public class JavassistFactory {

    public static Type typeUsageFor(CtClass ctClazz, TypeSolver typeSolver) {
        try {
            if (ctClazz.isArray()) {
                return new ArrayType(typeUsageFor(ctClazz.getComponentType(), typeSolver));
            } else if (ctClazz.isPrimitive()) {
                if (ctClazz.getName().equals("void")) {
                    return VoidType.INSTANCE;
                } else {
                    return PrimitiveType.byName(ctClazz.getName());
                }
            } else {
                if (ctClazz.isInterface()) {
                    return new ReferenceTypeImpl(new JavassistInterfaceDeclaration(ctClazz, typeSolver), typeSolver);
                } else {
                    return new ReferenceTypeImpl(new JavassistClassDeclaration(ctClazz, typeSolver), typeSolver);
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
            return new JavassistEnumDeclaration(ctClazz, typeSolver);
        } else if (ctClazz.isAnnotation()) {
            throw new UnsupportedOperationException("CtClass of annotation not yet supported");
        } else if (ctClazz.isArray()) {
            throw new IllegalArgumentException("This method should not be called passing an array");
        } else {
            return new JavassistClassDeclaration(ctClazz, typeSolver);
        }
    }
}
