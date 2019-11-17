/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.printer.PrettyPrinterConfiguration;

/**
 * This interface describes the different ways in which a node can be converted to a string.
 *
 * See this blog post for additional details: https://javaparser.org/making-strings-in-javaparser/
 */
public interface NodeAsString {

    /**
     * Description mostly from <a href="https://javaparser.org/making-strings-in-javaparser/">https://javaparser.org/making-strings-in-javaparser/</a>
     * <p>
     * We noticed that many people were using the output of the pretty printer
     * for comparisons, like <pre>name.toString.equals("a.b.C")</pre>
     *
     * This can easily lead to bugs, since the pretty printer will also output
     * comments and annotations associated with the node, so its output could be
     * easily be <pre>\/*hello*\/a.b.C</pre>! Oops!
     * <p>
     * {@link #asString()} is defined as "the output you probably want when you
     * want to represent this node as a string."
     * It is quite arbitrary, but mostly means "what toString does, but without
     * formatting, comments, or annotations."
     *
     * @return The node as a code string, normalised to not include the "fluff" that doesn't necessarily
     * affect meaning or execution of the code, such as comments and annotations.
     */
    String asString();


    /**
     * @return The pretty printer that will be used by {@link #toString()} and {@link #toPrettyString()} if no parameter is provided.
     */
    PrettyPrinterConfiguration getDefaultPrinterConfiguration();


    /**
     * This just delegates to {@link #toPrettyString()}.
     * <p>
     * Use of {@link #toString()} and {@link #toString(PrettyPrinterConfiguration)} is discouraged, in favour of:
     * <ul>
     *      <li>{@link #asString()} if you want a stable string representation that doesn't alter due to comments and similar volatile attributes</li>
     *      <li>{@link #toPrettyString()} if you want a formatted version of the node, using the default pretty-printer</li>
     *      <li>{@link #toString(PrettyPrinterConfiguration)} ()} if you want a formatted version of the node, using the default pretty-printer</li>
     * </ul>
     *
     * @return The output of {@link #toPrettyString()}
     */
    @Override
    String toString();

    /**
     * This just delegates to {@link #toPrettyString(PrettyPrinterConfiguration)}.
     * <p>
     * Use of {@link #toString()} and {@link #toString(PrettyPrinterConfiguration)} is discouraged, in favour of:
     * <ul>
     *      <li>{@link #asString()} if you want a stable string representation that doesn't alter due to comments and similar volatile attributes</li>
     *      <li>{@link #toPrettyString()} if you want a formatted version of the node, using the default pretty-printer</li>
     *      <li>{@link #toString(PrettyPrinterConfiguration)} ()} if you want a formatted version of the node, using the default pretty-printer</li>
     * </ul>
     *
     * @param prettyPrinterConfiguration A custom configuration describing the pretty-printing rules.
     * @return the output of {@link #toPrettyString(PrettyPrinterConfiguration)}
     */
    String toString(PrettyPrinterConfiguration prettyPrinterConfiguration);


    /**
     * This method calls {@link #toString(PrettyPrinterConfiguration)} with the default pretty printer.
     * @return This node as a pretty-printed String.
     */
    String toPrettyString();

    /**
     * See {@link #toPrettyString()} ()} for an overloaded equivalent which uses the default pretty-printer.
     *
     * @param prettyPrinterConfiguration A custom configuration describing the pretty-printing rules.
     * @return This node as a pretty-printed String.
     */
    String toPrettyString(PrettyPrinterConfiguration prettyPrinterConfiguration);

}
