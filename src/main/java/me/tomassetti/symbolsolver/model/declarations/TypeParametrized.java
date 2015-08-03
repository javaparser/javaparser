package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.TypeParameter;

import java.util.List;

/**
 * Created by federico on 03/08/15.
 */
public interface TypeParametrized {

    public List<TypeParameter> getTypeParameters();
}
