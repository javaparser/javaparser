package me.tomassetti.symbolsolver.model.javassist;

import javassist.CtClass;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.declarations.ArrayTypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.PrimitiveTypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;

/**
 * Created by federico on 20/08/15.
 */
public class JavassistFactory {

    public static TypeDeclaration typeDeclarationFor(CtClass ctClazz) {
        try {
            if (ctClazz.isArray()) {
                return new ArrayTypeDeclaration(typeDeclarationFor(ctClazz.getComponentType()));
            } else if (ctClazz.isPrimitive()) {
                return PrimitiveTypeDeclaration.byName(ctClazz.getName());
            } else {
                return new JavassistClassDeclaration(ctClazz);
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }
}
