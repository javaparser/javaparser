package com.github.javaparser.ast.lexical;

/**
 * @author Didier Villevalois
 */
public class Identifier extends Lexeme {

    private final String image;

    public Identifier(String image) {
        this.image = image;
    }

    @Override
    public LexemeKind getLexemeKind() {
        return LexemeKind.IDENTIFIER;
    }

    @Override
    public String image() {
        return image;
    }
}
