package com.github.javaparser.ast.validator;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.Node;

/**
 * Stub validator for when no validation is wanted.
 *
 * @deprecated when setting a language validator, try {@link com.github.javaparser.ParserConfiguration#setLanguageLevel(ParserConfiguration.LanguageLevel)} with RAW.
 */
@Deprecated
public final class NoProblemsValidator implements Validator {
    @Override
    public void accept(Node node, ProblemReporter problemReporter) {
    }
}
