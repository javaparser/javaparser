/*
 * Copyright (C) 2015 The JavaParser Team.
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

import java.util.List;

import com.github.javaparser.ast.Node;

/**
 * This class represents the result of parsing source code. It contains the
 * {@link Node} that has been constructed as a result of parsing and a list of
 * {@link Token}s thats have been encountered while building tokens for the
 * input.
 * 
 * @author Sebastian Kuerten
 */
public class ParseResult<T extends Node>
{

    private T node;
    private List<Token> tokens;

    ParseResult(T node, List<Token> tokens)
    {
        this.node = node;
        this.tokens = tokens;
    }

    /**
     * Get the node that this result represents
     * 
     * @return a subclass of {@link Node}
     */
    public T getNode() {
        return node;
    }

    /**
     * Get the list of {@link Token}s of the input
     * 
     * @return the list of tokens
     */
    public List<Token> getTokens() {
        return tokens;
    }

}
