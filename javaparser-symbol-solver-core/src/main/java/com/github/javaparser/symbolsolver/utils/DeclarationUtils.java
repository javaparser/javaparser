package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;

public class DeclarationUtils {
    public static boolean IsPublicStaticField(ResolvedValueDeclaration declaration) {
        if(declaration instanceof ResolvedFieldDeclaration) {
            ResolvedFieldDeclaration resolvedFieldDeclaration = (ResolvedFieldDeclaration)declaration;
            if(resolvedFieldDeclaration.isStatic() && resolvedFieldDeclaration.accessSpecifier() == AccessSpecifier.PUBLIC) {
                return true;
            };
        }

        return declaration instanceof ResolvedEnumConstantDeclaration;
    }
}
