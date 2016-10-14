package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

/**
 * Declaration of a value.
 *
 * @author Federico Tomassetti
 */
public interface ValueDeclaration extends Declaration {

    Type getType();

}
