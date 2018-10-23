package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.ParserConfiguration;

public class LeanParserConfiguration extends ParserConfiguration {
    public LeanParserConfiguration() {
        setLanguageLevel(ParserConfiguration.LanguageLevel.RAW);
        setStoreTokens(false);
        setAttributeComments(false);
        setLexicalPreservationEnabled(false);
    }
}
