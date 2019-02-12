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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.CommentsCollection;

import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;

import static com.github.javaparser.utils.Utils.EOL;

/**
 * The results given when parsing with an instance of JavaParser.
 */
public class ParseResult<T> {
    private final T result;
    private final List<Problem> problems;
    private final CommentsCollection commentsCollection;

    /**
     * General constructor.
     *
     * @param result the AST, or empty if it wasn't created.
     * @param problems a list of encountered parsing problems.
     */
    public ParseResult(T result, List<Problem> problems, CommentsCollection commentsCollection) {
        this.commentsCollection = commentsCollection;
        this.result = result;
        this.problems = problems;
    }

    /**
     * @return if parsing was successful, meaning no errors of any kind were encountered.
     */
    public boolean isSuccessful() {
        return problems.isEmpty() && result != null;
    }

    /**
     * Calls the consumer with the result if parsing was succesful.
     */
    public void ifSuccessful(Consumer<T> consumer) {
        if (isSuccessful()) {
            consumer.accept(result);
        }
    }

    /**
     * @return the list of encountered parsing problems. Empty when no problems were encountered.
     */
    public List<Problem> getProblems() {
        return problems;
    }

    /**
     * @return the <code>i</code>'th encountered parsing problem. May throw <code>IndexOutOfBoundsException</code>.
     */
    public Problem getProblem(int i) {
        return getProblems().get(i);
    }

    /**
     * @return the complete collection of comments encountered while parsing.
     */
    public Optional<CommentsCollection> getCommentsCollection() {
        return Optional.ofNullable(commentsCollection);
    }

    /**
     * @return the AST of the parsed source code, or empty if parsing failed completely.
     */
    public Optional<T> getResult() {
        return Optional.ofNullable(result);
    }

    @Override
    public String toString() {
        if (isSuccessful()) {
            return "Parsing successful";
        }
        StringBuilder message = new StringBuilder("Parsing failed:").append(EOL);
        for (Problem problem : problems) {
            message.append(problem.toString()).append(EOL);
        }
        return message.toString();
    }

    /**
     * A post processor that can be added to ParserConfiguration to add some processing right after parsing.
     */
    public interface PostProcessor {
        void process(ParseResult<? extends Node> result, ParserConfiguration configuration);
    }
}
