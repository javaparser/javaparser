package me.tomassetti.symbolsolver.model;

import java.util.List;

/**
 * Created by federico on 30/07/15.
 */
public interface ClassDeclaration extends TypeDeclaration {

    public List<TypeParameter> getTypeParameters();

}
