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

package com.github.javaparser.printer.lexicalpreservation;

public interface TextElementMatcher {

    boolean match(TextElement textElement);

    /**
     * This allows the combination of different TextElementMatcher instances.<br/>
     * If combined, all of the TextElementMatchers have to return true.
     *
     * @param textElementMatcher TextElementMatcher to combine with this one
     * @return A new and combined TextElementMatcher of this and textElementMatcher
     */
    default TextElementMatcher and(TextElementMatcher textElementMatcher) {
        return textElement -> this.match(textElement) && textElementMatcher.match(textElement);
    }
}
