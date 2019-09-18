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

import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.javadoc.Javadoc;
import com.github.javaparser.javadoc.JavadocBlockTag;
import com.github.javaparser.javadoc.description.JavadocDescription;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static com.github.javaparser.utils.Utils.*;

/**
 * The class responsible for parsing the content of JavadocComments and producing JavadocDocuments.
 * <a href="https://docs.oracle.com/javase/1.5.0/docs/tooldocs/windows/javadoc.html">The Javadoc specification.</a>
 */
class JavadocParser {

    private static String BLOCK_TAG_PREFIX = "@";
    private static Pattern BLOCK_PATTERN = Pattern.compile("^\\s*" + BLOCK_TAG_PREFIX, Pattern.MULTILINE);

    public static Javadoc parse(JavadocComment comment) {
        return parse(comment.getContent());
    }

    public static Javadoc parse(String commentContent) {
        List<String> cleanLines = cleanLines(normalizeEolInTextBlock(commentContent, EOL));
        int indexOfFirstBlockTag = cleanLines.stream()
                .filter(JavadocParser::isABlockLine)
                .map(cleanLines::indexOf)
                .findFirst()
                .orElse(-1);
        List<String> blockLines;
        String descriptionText;
        if (indexOfFirstBlockTag == -1) {
            descriptionText = trimRight(String.join(EOL, cleanLines));
            blockLines = Collections.emptyList();
        } else {
            descriptionText = trimRight(String.join(EOL, cleanLines.subList(0, indexOfFirstBlockTag)));

            //Combine cleaned lines, but only starting with the first block tag till the end
            //In this combined string it is easier to handle multiple lines which actually belong together
            String tagBlock = cleanLines.subList(indexOfFirstBlockTag, cleanLines.size())
                .stream()
                .collect(Collectors.joining(EOL));

            //Split up the entire tag back again, considering now that some lines belong to the same block tag.
            //The pattern splits the block at each new line starting with the '@' symbol, thus the symbol
            //then needs to be added again so that the block parsers handles everything correctly.
            blockLines = BLOCK_PATTERN
                .splitAsStream(tagBlock)
                .filter(s1 -> !s1.isEmpty())
                .map(s -> BLOCK_TAG_PREFIX + s)
                .collect(Collectors.toList());
        }
        Javadoc document = new Javadoc(JavadocDescription.parseText(descriptionText));
        blockLines.forEach(l -> document.addBlockTag(parseBlockTag(l)));
        return document;
    }

    private static JavadocBlockTag parseBlockTag(String line) {
        line = line.trim().substring(1);
        String tagName = nextWord(line);
        String rest = line.substring(tagName.length()).trim();
        return new JavadocBlockTag(tagName, rest);
    }

    private static boolean isABlockLine(String line) {
        return line.trim().startsWith(BLOCK_TAG_PREFIX);
    }

    private static String trimRight(String string) {
        while (!string.isEmpty() && Character.isWhitespace(string.charAt(string.length() - 1))) {
            string = string.substring(0, string.length() - 1);
        }
        return string;
    }

    private static List<String> cleanLines(String content) {
        String[] lines = content.split(EOL);
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
        // drop empty lines at the beginning and at the end
        while (cleanedLines.size() > 0 && cleanedLines.get(0).trim().isEmpty()) {
            cleanedLines = cleanedLines.subList(1, cleanedLines.size());
        }
        while (cleanedLines.size() > 0 && cleanedLines.get(cleanedLines.size() - 1).trim().isEmpty()) {
            cleanedLines = cleanedLines.subList(0, cleanedLines.size() - 1);
        }
        return cleanedLines;
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
