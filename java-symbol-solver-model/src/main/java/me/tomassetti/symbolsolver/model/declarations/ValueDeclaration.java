package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

/**
 * Declaration of a value.
 *
 * @author Federico Tomassetti
 */
public interface ValueDeclaration extends Declaration {

    TypeUsage getType();

}
