package com.github.javaparser.printer.concretesyntaxmodel;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.GeneratedModuleInfoParserConstants;

/**
 * Support for multiple grammars.
 */
public interface SourceGrammar {
    SourceGrammar JAVAPARSER = tokenType -> GeneratedJavaParserConstants.tokenImage[tokenType];
    SourceGrammar MODULE_INFO = tokenType -> GeneratedModuleInfoParserConstants.tokenImage[tokenType];

    String getTokenImage(int tokenType);
}
