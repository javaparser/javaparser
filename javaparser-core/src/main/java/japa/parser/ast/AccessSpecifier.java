package japa.parser.ast;

/**
 * Access specifier. Represents one of the possible levels of
 * access permitted by the language.
 *
 * @author Federico Tomassetti
 * @since July 2014
 */
public enum AccessSpecifier {

    PUBLIC("public"),
    PRIVATE("private"),
    PROTECTED("protected"),
    DEFAULT("");

    private String codeRepresenation;

    private AccessSpecifier(String codeRepresentation) {
        this.codeRepresenation = codeRepresentation;
    }

    public String getCodeRepresenation(){
        return this.codeRepresenation;
    }
}
