package me.tomassetti.symbolsolver.model;

import java.util.Optional;

/**
 * Created by federico on 28/07/15.
 */
public class SymbolReference<S extends SymbolDeclaration> {

    private Optional<S> correspondingDeclaration;

    public static <S extends SymbolDeclaration> SymbolReference<S> solved(S symbolDeclaration){
        return new SymbolReference(Optional.of(symbolDeclaration));
    }

    public static <S extends SymbolDeclaration> SymbolReference<S> unsolved(Class<S> clazz){
        return new SymbolReference(Optional.<S>empty());
    }

    private SymbolReference(Optional<S> correspondingDeclaration){
        this.correspondingDeclaration = correspondingDeclaration;
    }

    public S getCorrespondingDeclaration(){
        if (!isSolved()) {
            throw new IllegalStateException();
        }
        return correspondingDeclaration.get();
    }

    public boolean isSolved() {
        return correspondingDeclaration.isPresent();
    }
}
