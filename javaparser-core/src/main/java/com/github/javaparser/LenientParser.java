package com.github.javaparser;

import com.github.javaparser.JavaToken;

import com.github.javaparser.utils.LineSeparator;

import static com.github.javaparser.GeneratedJavaParserConstants.*;

import com.github.javaparser.TokenTypes;
public class LenientParser {


    LenientToken token;

    public static class IllegalTokenException extends IllegalArgumentException {
        public IllegalTokenException(String errorMessage) {
            super(errorMessage);
        }
    }

    public LenientParser(LenientToken token){

        this.token = token;
    }

    public LenientToken parseToken() throws ParseProblemException {




        return token;
    }






}
