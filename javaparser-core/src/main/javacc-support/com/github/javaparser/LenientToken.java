package com.github.javaparser;

public class LenientToken {

    private int kind;


    public JavaToken.Category getCategory() {
        return TokenTypes.getCategory(kind);
    }


    public LenientToken (JavaToken token){

        JavaToken.Category Double = null;
        JavaToken.Category Float = null;
        if (getCategory() == Double || getCategory() == Float) {
            
        }

        if (token.getCategory() == TokenTypes.getCategory(56)) {

            JavaToken replacement = new JavaToken(0);

            LenientToken replacementToken = new LenientToken(replacement);



        }

    }





}
