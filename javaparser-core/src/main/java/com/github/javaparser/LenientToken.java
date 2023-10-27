package com.github.javaparser;

public class LenientToken {

    private int kind;


    public JavaToken.Category getCategory() {
        return TokenTypes.getCategory(kind);
    }


    public LenientToken (TokenTypes token){

        JavaToken.Category Double = null;
        JavaToken.Category Float = null;
        if (getCategory() == Double || getCategory() == Float) {
            
        }
    }


}
