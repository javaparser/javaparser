/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.UnicodeEscapeProcessingProvider.PositionMapping;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.Validator;
import com.github.javaparser.ast.validator.language_level_validations.*;
import com.github.javaparser.ast.validator.postprocessors.*;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.utils.LineSeparator;

import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.function.Supplier;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.POPULAR;

/**
 * The configuration that is used by the parser.
 * Note that this can be changed even when reusing the same JavaParser instance.
 * It will pick up the changes.
 */
public class ParserConfiguration {

    public enum LanguageLevel {

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
         * Java 10 -- including incubator/preview/second preview features.
         * Note that preview features, unless otherwise specified, follow the grammar and behaviour of the latest released JEP for that feature.
         */
        JAVA_10_PREVIEW(new Java10PreviewValidator(), new Java10PostProcessor()),
        /**
         * Java 11
         */
        JAVA_11(new Java11Validator(), new Java11PostProcessor()),
        /**
         * Java 11 -- including incubator/preview/second preview features.
         * Note that preview features, unless otherwise specified, follow the grammar and behaviour of the latest released JEP for that feature.
         */
        JAVA_11_PREVIEW(new Java11PreviewValidator(), new Java11PostProcessor()),
        /**
         * Java 12
         */
        JAVA_12(new Java12Validator(), new Java12PostProcessor()),
        /**
         * Java 12 -- including incubator/preview/second preview features.
         * Note that preview features, unless otherwise specified, follow the grammar and behaviour of the latest released JEP for that feature.
         * <ul>
         *     <li>Switch expressions are permitted, with a single label only and no yield.</li>
         * </ul>
         */
        JAVA_12_PREVIEW(new Java12PreviewValidator(), new Java12PostProcessor()),
        /**
         * Java 13
         */
        JAVA_13(new Java13Validator(), new Java13PostProcessor()),
        /**
         * Java 13 -- including incubator/preview/second preview features.
         * Note that preview features, unless otherwise specified, follow the grammar and behaviour of the latest released JEP for that feature.
         * <ul>
         *     <li>Switch expressions are permitted, with a single label only.</li>
         * </ul>
         */
        JAVA_13_PREVIEW(new Java13PreviewValidator(), new Java13PostProcessor()),
        /**
         * Java 14
         */
        JAVA_14(new Java14Validator(), new Java14PostProcessor()),
        /**
         * Java 14 -- including incubator/preview/second preview features.
         * Note that preview features, unless otherwise specified, follow the grammar and behaviour of the latest released JEP for that feature.
         */
        JAVA_14_PREVIEW(new Java14PreviewValidator(), new Java14PostProcessor()),
        /**
         * Java 15
         */
        JAVA_15(new Java15Validator(), new Java15PostProcessor()),
        /**
         * Java 15 -- including incubator/preview/second preview features.
         * Note that preview features, unless otherwise specified, follow the grammar and behaviour of the latest released JEP for that feature.
         */
        JAVA_15_PREVIEW(new Java15PreviewValidator(), new Java15PostProcessor()),
        /**
         * Java 16
         */
        JAVA_16(new Java16Validator(), new Java16PostProcessor()),
        /**
         * Java 16 -- including incubator/preview/second preview features.
         * Note that preview features, unless otherwise specified, follow the grammar and behaviour of the latest released JEP for that feature.
         */
        JAVA_16_PREVIEW(new Java16PreviewValidator(), new Java16PostProcessor()),
        /**
         * Java 17
         */
        JAVA_17(new Java17Validator(), new Java17PostProcessor()),
        /**
         * Java 17 -- including incubator/preview/second preview features.
         * Note that preview features, unless otherwise specified, follow the grammar and behaviour of the latest released JEP for that feature.
         */
        JAVA_17_PREVIEW(new Java17PreviewValidator(), new Java17PostProcessor());

        /**
         * Does no post processing or validation. Only for people wanting the fastest parsing.
         */
        public static LanguageLevel RAW = null;

        /**
         * The most used Java version.
         */
        public static LanguageLevel POPULAR = JAVA_11;

        /**
         * The latest Java version that is available.
         */
        public static LanguageLevel CURRENT = JAVA_16;

        /**
         * The newest Java features supported.
         */
        public static LanguageLevel BLEEDING_EDGE = JAVA_17_PREVIEW;

        final Validator validator;

        final PostProcessors postProcessor;

        private static final LanguageLevel[] yieldSupport = new LanguageLevel[] { JAVA_13, JAVA_13_PREVIEW, JAVA_14, JAVA_14_PREVIEW, JAVA_15, JAVA_15_PREVIEW, JAVA_16, JAVA_16_PREVIEW, JAVA_17, JAVA_17_PREVIEW };

        LanguageLevel(Validator validator, PostProcessors postProcessor) {
            this.validator = validator;
            this.postProcessor = postProcessor;
        }

        public boolean isYieldSupported() {
            return Arrays.stream(yieldSupport).anyMatch(level -> level == this);
        }
    }

    // TODO: Add a configurable option e.g. setDesiredLineEnding(...) to replace/swap out existing line endings
    private boolean detectOriginalLineSeparator = true;

    private boolean storeTokens = true;

    private boolean attributeComments = true;

    private boolean doNotAssignCommentsPrecedingEmptyLines = true;

    private boolean ignoreAnnotationsWhenAttributingComments = false;

    private boolean lexicalPreservationEnabled = false;

    private boolean preprocessUnicodeEscapes = false;

    private SymbolResolver symbolResolver = null;

    private int tabSize = 1;

    private LanguageLevel languageLevel = POPULAR;

    private Charset characterEncoding = Providers.UTF8;

    private final List<Supplier<Processor>> processors = new ArrayList<>();

    private class UnicodeEscapeProcessor extends Processor {

        private UnicodeEscapeProcessingProvider _unicodeDecoder;

        @Override
        public Provider preProcess(Provider innerProvider) {
            if (isPreprocessUnicodeEscapes()) {
                _unicodeDecoder = new UnicodeEscapeProcessingProvider(innerProvider);
                return _unicodeDecoder;
            }
            return innerProvider;
        }

        @Override
        public void postProcess(ParseResult<? extends Node> result, ParserConfiguration configuration) {
            if (isPreprocessUnicodeEscapes()) {
                result.getResult().ifPresent(root -> {
                    PositionMapping mapping = _unicodeDecoder.getPositionMapping();
                    if (!mapping.isEmpty()) {
                        root.walk(node -> node.getRange().ifPresent(range -> node.setRange(mapping.transform(range))));
                    }
                });
            }
        }
    }

    private class LineEndingProcessor extends Processor {

        private LineEndingProcessingProvider _lineEndingProcessingProvider;

        @Override
        public Provider preProcess(Provider innerProvider) {
            if (isDetectOriginalLineSeparator()) {
                _lineEndingProcessingProvider = new LineEndingProcessingProvider(innerProvider);
                return _lineEndingProcessingProvider;
            }
            return innerProvider;
        }

        @Override
        public void postProcess(ParseResult<? extends Node> result, ParserConfiguration configuration) {
            if (isDetectOriginalLineSeparator()) {
                result.getResult().ifPresent(rootNode -> {
                    LineSeparator detectedLineSeparator = _lineEndingProcessingProvider.getDetectedLineEnding();
                    // Set the line ending on the root node
                    rootNode.setData(Node.LINE_SEPARATOR_KEY, detectedLineSeparator);
                    // // Set the line ending on all children of the root node -- FIXME: Should ignore """textblocks"""
                    // rootNode.findAll(Node.class)
                    // .forEach(node -> node.setData(Node.LINE_SEPARATOR_KEY, detectedLineSeparator));
                });
            }
        }
    }

    public ParserConfiguration() {
        processors.add(() -> ParserConfiguration.this.new UnicodeEscapeProcessor());
        processors.add(() -> ParserConfiguration.this.new LineEndingProcessor());
        processors.add(() -> new Processor() {

            @Override
            public void postProcess(ParseResult<? extends Node> result, ParserConfiguration configuration) {
                if (configuration.isAttributeComments()) {
                    result.ifSuccessful(resultNode -> result.getCommentsCollection().ifPresent(comments -> new CommentsInserter(configuration).insertComments(resultNode, comments.copy().getComments())));
                }
            }
        });
        processors.add(() -> new Processor() {

            @Override
            public void postProcess(ParseResult<? extends Node> result, ParserConfiguration configuration) {
                LanguageLevel languageLevel = getLanguageLevel();
                if (languageLevel != null) {
                    if (languageLevel.postProcessor != null) {
                        languageLevel.postProcessor.postProcess(result, configuration);
                    }
                    if (languageLevel.validator != null) {
                        languageLevel.validator.accept(result.getResult().get(), new ProblemReporter(newProblem -> result.getProblems().add(newProblem)));
                    }
                }
            }
        });
        processors.add(() -> new Processor() {

            @Override
            public void postProcess(ParseResult<? extends Node> result, ParserConfiguration configuration) {
                configuration.getSymbolResolver().ifPresent(symbolResolver -> result.ifSuccessful(resultNode -> {
                    if (resultNode instanceof CompilationUnit) {
                        resultNode.setData(Node.SYMBOL_RESOLVER_KEY, symbolResolver);
                    }
                }));
            }
        });
        processors.add(() -> new Processor() {

            @Override
            public void postProcess(ParseResult<? extends Node> result, ParserConfiguration configuration) {
                if (configuration.isLexicalPreservationEnabled()) {
                    result.ifSuccessful(LexicalPreservingPrinter::setup);
                }
            }
        });
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

    public List<Supplier<Processor>> getProcessors() {
        return processors;
    }

    public ParserConfiguration setLanguageLevel(LanguageLevel languageLevel) {
        this.languageLevel = languageLevel;
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

    public ParserConfiguration setDetectOriginalLineSeparator(boolean detectOriginalLineSeparator) {
        this.detectOriginalLineSeparator = detectOriginalLineSeparator;
        return this;
    }

    public boolean isDetectOriginalLineSeparator() {
        return detectOriginalLineSeparator;
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
