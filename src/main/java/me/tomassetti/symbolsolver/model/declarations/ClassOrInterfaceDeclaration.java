package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.TypeParameter;

import java.util.List;

/**
 * A class or interface declaration.
 */
public interface ClassOrInterfaceDeclaration extends TypeDeclaration {
    public List<TypeParameter> getTypeParameters();
}
