package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.TypeParameter;

import java.util.List;

/**
 * Created by federico on 30/07/15.
 */
public interface ClassDeclaration extends TypeDeclaration {

    public List<TypeParameter> getTypeParameters();

}
