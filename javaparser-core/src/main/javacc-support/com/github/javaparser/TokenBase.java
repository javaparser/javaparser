package com.github.javaparser;

import static com.github.javaparser.GeneratedJavaParserConstants.GT;

/**
 * Base class for the generated {@link Token}
 */
abstract class TokenBase {
    /**
     * For tracking the >> >>> ambiguity.
     */
    int realKind = GT;
    
    /**
     * This is the link to the token that JavaParser presents to the user
     */
    JavaToken javaToken = null;
}
