package com.github.javaparser;

import com.github.javaparser.JavaToken;

import com.github.javaparser.utils.LineSeparator;

import static com.github.javaparser.GeneratedJavaParserConstants.*;

import com.github.javaparser.TokenTypes;

import java.util.Scanner;

import java.util.*;

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

    public static boolean isFloatOrDoubleCharacter(char c) {
        // Use regular expressions to match characters that are part of a float or double
        if (Character.isDigit(c) || c == '.' || c == 'E' || c == 'e' || c == '-' || c == '+') {
            return true;
        }
        return false;
    }


    static int parseInt(Scanner input) throws ParseException {



        while (input.hasNext()){

            char operator = input.next().charAt(0);

            if (isFloatOrDoubleCharacter(operator)){

                JavaToken testToken = new JavaToken(23);
            }


        }

        return 0;
    }

    static class ParseException extends Exception {
        public ParseException(String message) {
            super(message);
        }
    }






}
