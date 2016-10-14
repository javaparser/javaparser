package me.tomassetti.symbolsolver.model.declarations;

import java.util.List;

/**
 * An entity which has type parameter.
 *
 * @author Federico Tomassetti
 */
public interface TypeParametrizable {

    List<TypeParameterDeclaration> getTypeParameters();

}
