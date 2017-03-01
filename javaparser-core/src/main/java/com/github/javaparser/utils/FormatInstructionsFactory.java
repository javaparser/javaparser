package com.github.javaparser.utils;

/**
 * A factory for retrieving different formatting instructions.
 *
 * @version 3.1.0
 * @since 3.1.0
 * @see TreeStructureVisitor
 * @author Ryan Beckett
 *
 */
public class FormatInstructionsFactory {

    private final static DefaultFormatInstructions DEFAULT_FORMAT_INSTANCE = new DefaultFormatInstructions();
    private final static XMLFormatInstructions XML__FORMAT_INSTANCE = new XMLFormatInstructions();
    private final static JSONFormatInstructions JSON_FORMAT_INSTANCE = new JSONFormatInstructions();

    public static enum Format {
        DEFAULT, XML, JSON
    };

    public static FormatInstructions getFormatInstructions() {
        return getFormatInstructions(Format.DEFAULT);
    }

    public static FormatInstructions getFormatInstructions(Format format) {
        switch (format) {
            case XML:
                return XML__FORMAT_INSTANCE;
            case JSON:
                return JSON_FORMAT_INSTANCE;
            default:
                return DEFAULT_FORMAT_INSTANCE;
        }
    }

}
