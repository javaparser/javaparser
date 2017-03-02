package com.github.javaparser.utils.format;

/**
 * A factory for retrieving different formatting instructions.
 *
 * @version 3.1.0
 * @since 3.1.0
 * @see TreeStructureVisitor
 * @see Format
 * @author Ryan Beckett
 *
 */
public class FormatInstructionsFactory {

    private final static DefaultFormatInstructions DEFAULT_FORMAT_INSTANCE = new DefaultFormatInstructions();
    private final static XMLFormatInstructions XML__FORMAT_INSTANCE = new XMLFormatInstructions();
    private final static JSONFormatInstructions JSON_FORMAT_INSTANCE = new JSONFormatInstructions();

    /**
     * Get the singleton instance of the default formatting instructions.
     *
     * @return The instructions for the default format.
     */
    public static FormatInstructions getFormatInstructions() {
        return getFormatInstructions(Format.DEFAULT);
    }

    /**
     * Get the singleton instance of the specified formatting instructions.
     *
     * @param format The format whose instructions are to be retrieved.
     *
     * @return The corresponding instructions for the given format.
     */
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
