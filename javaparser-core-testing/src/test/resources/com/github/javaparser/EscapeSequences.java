package com.github.javaparser;

public class EscapeSequences {

    public static void main(String[] args) {
        Object[] chars = {
                '\\', '\u005C\u005C', '\u005c\u005c',
                "---",
                '\n', '\u005cn', '\u005Cn',
                "---",
                '\r', '\u005cr', '\u005Cr',
                "---",
                '\t', '\u005ct', '\u005Ct',
                "---",
                '\b', '\u005cb', '\u005Cb',
                "---",
                '\f', '\u005cf', '\u005Cf',
                "---",
                '\'', '\u005c'', // '\u005C'', // that's weird, this last one won't compile
                "---",
                '\"', '\u005c"', '\u005C"'
        };
        for (Object obj : chars) {
            if (obj instanceof Character) {
                System.out.println(obj + " " + (int) (char) obj); // print the numeric representation
            } else {
                System.out.println(obj);
            }
        }
    }

}
