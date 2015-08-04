package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.TypeParameter;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 03/08/15.
 */
public interface TypeParametrized {

    public List<TypeParameter> getTypeParameters();

}
