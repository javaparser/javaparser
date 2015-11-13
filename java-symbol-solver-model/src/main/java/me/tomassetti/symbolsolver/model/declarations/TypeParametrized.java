package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.resolution.TypeParameter;

import java.util.List;

/**
 * @author Federico Tomassetti
 */
public interface TypeParametrized {

    public List<TypeParameter> getTypeParameters();

}
