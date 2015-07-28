package me.tomassetti.symbolsolver.model;

import java.util.Optional;

/**
 * Created by federico on 28/07/15.
 */
public class SymbolReference {

    private Optional<SymbolDeclaration> correspondingDeclaration;

    public static SymbolReference solved(SymbolDeclaration symbolDeclaration){
        return new SymbolReference(Optional.of(symbolDeclaration));
    }

    public static SymbolReference unsolved(){
        return new SymbolReference(Optional.<SymbolDeclaration>empty());
    }

    private SymbolReference(Optional<SymbolDeclaration> correspondingDeclaration){
        this.correspondingDeclaration = correspondingDeclaration;
    }

    public SymbolDeclaration getCorrespondingDeclaration(){
        if (!isSolved()) {
            throw new IllegalStateException();
        }
        return correspondingDeclaration.get();
    }

    public boolean isSolved() {
        return correspondingDeclaration.isPresent();
    }
}
