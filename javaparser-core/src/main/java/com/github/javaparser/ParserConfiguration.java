/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.*;
import static com.github.javaparser.utils.Utils.*;

import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import com.github.javaparser.ParseResult.PostProcessor;
import com.github.javaparser.Providers.PreProcessor;
import com.github.javaparser.UnicodeEscapeProcessingProvider.PositionMapping;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.validator.Java10Validator;
import com.github.javaparser.ast.validator.Java11Validator;
import com.github.javaparser.ast.validator.Java12Validator;
import com.github.javaparser.ast.validator.Java1_0Validator;
import com.github.javaparser.ast.validator.Java1_1Validator;
import com.github.javaparser.ast.validator.Java1_2Validator;
import com.github.javaparser.ast.validator.Java1_3Validator;
import com.github.javaparser.ast.validator.Java1_4Validator;
import com.github.javaparser.ast.validator.Java5Validator;
import com.github.javaparser.ast.validator.Java6Validator;
import com.github.javaparser.ast.validator.Java7Validator;
import com.github.javaparser.ast.validator.Java8Validator;
import com.github.javaparser.ast.validator.Java9Validator;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.Validator;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.version.Java10PostProcessor;
import com.github.javaparser.version.Java11PostProcessor;
import com.github.javaparser.version.Java12PostProcessor;

/**
 * The configuration that is used by the parser.
 * Note that this can be changed even when reusing the same JavaParser instance.
 * It will pick up the changes.
 */
public class ParserConfiguration {
    public enum LanguageLevel {
        /**
         * Does no post processing or validation. Only for people wanting the fastest parsing.
         */
        RAW(null, null),
        /**
         * The most used Java version.
         */
        POPULAR(new Java8Validator(), null),
        /**
         * The latest Java version that is available.
         */
        CURRENT(new Java8Validator(), null),
        /**
         * The newest Java features supported.
         */
        BLEEDING_EDGE(new Java12Validator(), new Java12PostProcessor()),
        /**
         * Java 1.0
         */
        JAVA_1_0(new Java1_0Validator(), null),
        /**
         * Java 1.1
         */
        JAVA_1_1(new Java1_1Validator(), null),
        /**
         * Java 1.2
         */
        JAVA_1_2(new Java1_2Validator(), null),
        /**
         * Java 1.3
         */
        JAVA_1_3(new Java1_3Validator(), null),
        /**
         * Java 1.4
         */
        JAVA_1_4(new Java1_4Validator(), null),
        /**
         * Java 5
         */
        JAVA_5(new Java5Validator(), null),
        /**
         * Java 6
         */
        JAVA_6(new Java6Validator(), null),
        /**
         * Java 7
         */
        JAVA_7(new Java7Validator(), null),
        /**
         * Java 8
         */
        JAVA_8(new Java8Validator(), null),
        /**
         * Java 9
         */
        JAVA_9(new Java9Validator(), null),
        /**
         * Java 10
         */
        JAVA_10(new Java10Validator(), new Java10PostProcessor()),
        /**
         * Java 11
         */
        JAVA_11(new Java11Validator(), new Java11PostProcessor()),
        /**
         * Java 12
         */
        JAVA_12(new Java12Validator(), new Java12PostProcessor());

        final Validator validator;
        final ParseResult.PostProcessor postProcessor;

        LanguageLevel(Validator validator, ParseResult.PostProcessor postProcessor) {
            this.validator = validator;
            this.postProcessor = postProcessor;
        }
    }

    private boolean storeTokens = true;
    private boolean attributeComments = true;
    private boolean doNotAssignCommentsPrecedingEmptyLines = true;
    private boolean ignoreAnnotationsWhenAttributingComments = false;
    private boolean lexicalPreservationEnabled = false;
    private boolean preprocessUnicodeEscapes = false;
    private SymbolResolver symbolResolver = null;
    private int tabSize = 1;
    private LanguageLevel languageLevel = CURRENT;
    private Charset characterEncoding = Providers.UTF8;

    private final List<Providers.PreProcessor> preProcessors = new ArrayList<>();
    private final List<ParseResult.PostProcessor> postProcessors = new ArrayList<>();

    public ParserConfiguration() {
    	class UnicodeEscapeProcessor implements PreProcessor, PostProcessor {
    		private UnicodeEscapeProcessingProvider _unicodeDecoder;

			@Override
    		public Provider process(Provider innerProvider) {
	            if (isPreprocessUnicodeEscapes()) {
	                _unicodeDecoder = new UnicodeEscapeProcessingProvider(innerProvider);
					return _unicodeDecoder;
	            }
	            return innerProvider;
    		}
    		
			@Override
			public void process(ParseResult<? extends Node> result,
					ParserConfiguration configuration) {
				if (isPreprocessUnicodeEscapes()) {
					result.getResult().ifPresent(
						root -> {
							PositionMapping mapping = _unicodeDecoder.getPositionMapping();
							if (!mapping.isEmpty()) {
								root.walk(
									node -> node.getRange().ifPresent(
										range -> node.setRange(mapping.transform(range))));
							}
						}
					);
				}
			}
    	}
    	UnicodeEscapeProcessor unicodeProcessor = new UnicodeEscapeProcessor();
    	preProcessors.add(unicodeProcessor);
		postProcessors.add(unicodeProcessor);
        postProcessors.add((result, configuration) -> {
            if (configuration.isLexicalPreservationEnabled()) {
                result.ifSuccessful(LexicalPreservingPrinter::setup);
            }
        });
        postProcessors.add((result, configuration) -> {
            if (configuration.isAttributeComments()) {
                result.ifSuccessful(resultNode -> result
                        .getCommentsCollection().ifPresent(comments ->
                                new CommentsInserter(configuration).insertComments(resultNode, comments.copy().getComments())));
            }
        });
        postProcessors.add((result, configuration) -> {
            LanguageLevel languageLevel = getLanguageLevel();
            if (languageLevel.postProcessor != null) {
                languageLevel.postProcessor.process(result, configuration);
            }
            if (languageLevel.validator != null) {
                languageLevel.validator.accept(result.getResult().get(), new ProblemReporter(newProblem -> result.getProblems().add(newProblem)));
            }
        });
        postProcessors.add((result, configuration) -> configuration.getSymbolResolver().ifPresent(symbolResolver ->
                result.ifSuccessful(resultNode -> {
                    if (resultNode instanceof CompilationUnit) {
                        resultNode.setData(Node.SYMBOL_RESOLVER_KEY, symbolResolver);
                    }
                })
        ));
    }

    public boolean isAttributeComments() {
        return attributeComments;
    }

    /**
     * Whether to run CommentsInserter, which will put the comments that were found in the source code into the comment
     * and javadoc fields of the nodes it thinks they refer to.
     */
    public ParserConfiguration setAttributeComments(boolean attributeComments) {
        this.attributeComments = attributeComments;
        return this;
    }

    public boolean isDoNotAssignCommentsPrecedingEmptyLines() {
        return doNotAssignCommentsPrecedingEmptyLines;
    }

    public ParserConfiguration setDoNotAssignCommentsPrecedingEmptyLines(boolean doNotAssignCommentsPrecedingEmptyLines) {
        this.doNotAssignCommentsPrecedingEmptyLines = doNotAssignCommentsPrecedingEmptyLines;
        return this;
    }

    public boolean isIgnoreAnnotationsWhenAttributingComments() {
        return ignoreAnnotationsWhenAttributingComments;
    }

    public ParserConfiguration setIgnoreAnnotationsWhenAttributingComments(boolean ignoreAnnotationsWhenAttributingComments) {
        this.ignoreAnnotationsWhenAttributingComments = ignoreAnnotationsWhenAttributingComments;
        return this;
    }

    public ParserConfiguration setStoreTokens(boolean storeTokens) {
        this.storeTokens = storeTokens;
        if (!storeTokens) {
            setAttributeComments(false);
        }
        return this;
    }

    public boolean isStoreTokens() {
        return storeTokens;
    }

    public int getTabSize() {
        return tabSize;
    }

    /**
     * When a TAB character is encountered during parsing, the column position will be increased by this value.
     * By default it is 1.
     */
    public ParserConfiguration setTabSize(int tabSize) {
        this.tabSize = tabSize;
        return this;
    }

    /**
     * Disabled by default.
     * When this is enabled, LexicalPreservingPrinter.print can be used to reproduce
     * the original formatting of the file.
     */
    public ParserConfiguration setLexicalPreservationEnabled(boolean lexicalPreservationEnabled) {
        this.lexicalPreservationEnabled = lexicalPreservationEnabled;
        return this;
    }

    public boolean isLexicalPreservationEnabled() {
        return lexicalPreservationEnabled;
    }

    /**
     * Retrieve the SymbolResolver to be used while parsing, if any.
     */
    public Optional<SymbolResolver> getSymbolResolver() {
        return Optional.ofNullable(symbolResolver);
    }

    /**
     * Set the SymbolResolver to be injected while parsing.
     */
    public ParserConfiguration setSymbolResolver(SymbolResolver symbolResolver) {
        this.symbolResolver = symbolResolver;
        return this;
    }

    public List<Providers.PreProcessor> getPreProcessors() {
        return preProcessors;
    }

    public List<ParseResult.PostProcessor> getPostProcessors() {
        return postProcessors;
    }

    public ParserConfiguration setLanguageLevel(LanguageLevel languageLevel) {
        this.languageLevel = assertNotNull(languageLevel);
        return this;
    }

    public LanguageLevel getLanguageLevel() {
        return languageLevel;
    }

    /**
     * When set to true, unicode escape handling is done by preprocessing the whole input,
     * meaning that all unicode escapes are turned into unicode characters before parsing.
     * That means the AST will never contain literal unicode escapes. However,
     * positions in the AST will point to the original input, which is exactly the same as without this option.
     * Without this option enabled, the unicode escapes will not be processed and are transfered intact to the AST.
     */
    public ParserConfiguration setPreprocessUnicodeEscapes(boolean preprocessUnicodeEscapes) {
        this.preprocessUnicodeEscapes = preprocessUnicodeEscapes;
        return this;
    }

    public boolean isPreprocessUnicodeEscapes() {
        return preprocessUnicodeEscapes;
    }

    public Charset getCharacterEncoding() {
        return characterEncoding;
    }

    /**
     * The character encoding used for reading input from files and streams. By default UTF8 is used.
     */
    public ParserConfiguration setCharacterEncoding(Charset characterEncoding) {
        this.characterEncoding = characterEncoding;
        return this;
    }

}
