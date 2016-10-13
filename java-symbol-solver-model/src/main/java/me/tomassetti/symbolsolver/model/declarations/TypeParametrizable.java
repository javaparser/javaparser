package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.resolution.TypeParameter;

import java.util.List;

/**
 * An entity which has type parameter.
 *
 * @author Federico Tomassetti
 */
public interface TypeParametrizable {

    List<TypeParameter> getTypeParameters();

}
