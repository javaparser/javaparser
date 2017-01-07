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

package com.github.javaparser.javadoc;

import com.github.javaparser.ast.comments.JavadocComment;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class JavadocParser {

    public JavadocDocument parse(JavadocComment comment) {
        return parse(comment.getContent());
    }

    public JavadocDocument parse(String commentContent) {
        List<String> cleanLines = cleanLines(commentContent);
        if (cleanLines.isEmpty()) {
            return new JavadocDocument(JavadocText.fromText(""));
        } else if (cleanLines.size() == 1) {
            String summaryText = trimRight(cleanLines.get(0));
            return new JavadocDocument(parseText(summaryText));
        } else {
            String summaryText = trimRight(cleanLines.get(0));
            String detailsText = trimRight(String.join("\n", cleanLines.subList(1, cleanLines.size())));
            if (detailsText.isEmpty()) {
                return new JavadocDocument(parseText(summaryText));
            }
            return new JavadocDocument(JavadocText.fromText(summaryText), JavadocText.fromText(detailsText));
        }
    }

    private String trimRight(String string) {
        while (string.endsWith(" ") || string.endsWith("\t")) {
            string = string.substring(0, string.length() - 1);
        }
        return string;
    }

    private JavadocText parseText(String content) {
        return JavadocText.fromText(content);
    }

    private List<String> cleanLines(String content) {
        String[] lines = content.split("\n");
        List<String> cleanedLines = Arrays.stream(lines).map(l -> {
                    int asteriskIndex = startsWithAsterisk(l);
                    if (asteriskIndex == -1) {
                        return l;
                    } else {
                        // if a line starts with space followed by an asterisk drop to the asterisk
                        // if there is a space immediately after the asterisk drop it also
                        if (l.length() > (asteriskIndex + 1)) {

                            char c = l.charAt(asteriskIndex + 1);
                            if (c == ' ' || c == '\t') {
                                return l.substring(asteriskIndex + 2);
                            }
                        }
                        return l.substring(asteriskIndex + 1);
                    }
                }).collect(Collectors.toList());
        // lines containing only whitespace are normalized to empty lines
        cleanedLines = cleanedLines.stream().map(l -> l.trim().isEmpty() ? "" : l).collect(Collectors.toList());
        // if the first starts with a space, remove it
        if (!cleanedLines.get(0).isEmpty() && (cleanedLines.get(0).charAt(0) == ' ' || cleanedLines.get(0).charAt(0) == '\t')) {
            cleanedLines.set(0, cleanedLines.get(0).substring(1));
        }
        // if the first line is empty, drop it
        if (cleanedLines.get(0).trim().length() == 0) {
            return cleanedLines.subList(1, cleanedLines.size());
        } else {
            return cleanedLines;
        }
    }

    // Visible for testing
    static int startsWithAsterisk(String line) {
        if (line.startsWith("*")) {
            return 0;
        } else if ((line.startsWith(" ") || line.startsWith("\t")) && line.length() > 1) {
            int res = startsWithAsterisk(line.substring(1));
            if (res == -1) {
                return -1;
            } else {
                return 1 + res;
            }
        } else {
            return -1;
        }
    }
}
