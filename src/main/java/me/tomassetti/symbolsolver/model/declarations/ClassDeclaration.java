package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.TypeParameter;

import java.util.List;

/**
 * A class declaration.
 * Not an interface declaration.
 */
public interface ClassDeclaration extends TypeDeclaration {

    public List<TypeParameter> getTypeParameters();

}
