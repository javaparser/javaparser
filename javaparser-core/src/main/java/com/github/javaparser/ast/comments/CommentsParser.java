/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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
 
package com.github.javaparser.ast.comments;

import java.io.*;
import java.nio.charset.Charset;
import java.util.*;

/**
 * This parser cares exclusively about comments.
 */
public class CommentsParser {

    private enum State {
        CODE,
        IN_LINE_COMMENT,
        IN_BLOCK_COMMENT,
        IN_STRING,
        IN_CHAR
    }

    private static final int COLUMNS_PER_TAB = 4;

    public CommentsCollection parse(final String source) throws IOException, UnsupportedEncodingException {
        InputStream in = new ByteArrayInputStream(source.getBytes(Charset.defaultCharset()));
        return parse(in, Charset.defaultCharset().name());
    }

    /**
     * Track the internal state of the parser, remembering the last characters observed.
     */
    class ParserState {
        private Deque prevTwoChars = new LinkedList<Character>();

        /**
         * Is the last character the one expected?
         */
        boolean isLastChar(char expectedChar) {
            return prevTwoChars.size() >= 1 && prevTwoChars.peekLast().equals(expectedChar);
        }

        /**
         * Is the character before the last one the same as expectedChar?
         */
        public boolean isSecondToLastChar(char expectedChar) {
            return prevTwoChars.size() >= 1 && prevTwoChars.peekFirst().equals(expectedChar);
        }

        /**
         * Record a new character. It will be the last one. The character that was the last one will
         * become the second to last one.
         */
        public void update(char c) {
            if (prevTwoChars.size() == 2) {
                prevTwoChars.remove();
            }
            prevTwoChars.add(c);
        }

        /**
         * Remove all the characters observed.
         */
        public void reset() {
            while (!prevTwoChars.isEmpty()) {
                prevTwoChars.removeFirst();
            }
        }
    }

    public CommentsCollection parse(final InputStream in, final String charsetName) throws IOException, UnsupportedEncodingException {
        boolean lastWasASlashR = false;
        BufferedReader br = new BufferedReader(new InputStreamReader(in, charsetName));
        CommentsCollection comments = new CommentsCollection();
        int r;

        ParserState parserState = new ParserState();

        State state = State.CODE;
        LineComment currentLineComment = null;
        BlockComment currentBlockComment = null;
        StringBuffer currentContent = null;

        int currLine = 1;
        int currCol  = 1;

        while ((r=br.read()) != -1){
            char c = (char)r;
            if (c=='\r'){
                lastWasASlashR = true;
            } else if (c=='\n'&&lastWasASlashR){
                lastWasASlashR=false;
                continue;
            } else {
                lastWasASlashR=false;
            }
            switch (state) {
                case CODE:
                    if (parserState.isLastChar('/') && c == '/') {
                        currentLineComment = new LineComment();
                        currentLineComment.setBeginLine(currLine);
                        currentLineComment.setBeginColumn(currCol - 1);
                        state = State.IN_LINE_COMMENT;
                        currentContent = new StringBuffer();
                    } else if (parserState.isLastChar('/') && c == '*') {
                        currentBlockComment = new BlockComment();
                        currentBlockComment.setBeginLine(currLine);
                        currentBlockComment.setBeginColumn(currCol - 1);
                        state = State.IN_BLOCK_COMMENT;
                        currentContent = new StringBuffer();
                    } else if (c == '"') {
                        state = State.IN_STRING;
                    } else if (c == '\'') {
                        state = State.IN_CHAR;
                    } else {
                        // nothing to do
                    }
                    break;
                case IN_LINE_COMMENT:
                    if (c=='\n' || c=='\r'){
                        currentLineComment.setContent(currentContent.toString());
                        currentLineComment.setEndLine(currLine);
                        currentLineComment.setEndColumn(currCol);
                        comments.addComment(currentLineComment);
                        state = State.CODE;
                    } else {
                        currentContent.append(c);
                    }
                    break;
                case IN_BLOCK_COMMENT:
                    // '/*/' is not a valid block comment: it starts the block comment but it does not close it
                    // However this sequence can be contained inside a comment and in that case it close the comment
                    // For example:
                    // /* blah blah /*/
                    // At the previous line we had a valid block comment
                    if (parserState.isLastChar('*') && c=='/' && (!parserState.isSecondToLastChar('/') || currentContent.length() > 0)){

                        // delete last character
                        String content = currentContent.deleteCharAt(currentContent.toString().length()-1).toString();

                        if (content.startsWith("*")){
                            JavadocComment javadocComment = new JavadocComment();
                            javadocComment.setContent(content.substring(1));
                            javadocComment.setBeginLine(currentBlockComment.getBeginLine());
                            javadocComment.setBeginColumn(currentBlockComment.getBeginColumn());
                            javadocComment.setEndLine(currLine);
                            javadocComment.setEndColumn(currCol+1);
                            comments.addComment(javadocComment);
                        } else {
                            currentBlockComment.setContent(content);
                            currentBlockComment.setEndLine(currLine);
                            currentBlockComment.setEndColumn(currCol+1);
                            comments.addComment(currentBlockComment);
                        }
                        state = State.CODE;
                    } else {
                        currentContent.append(c=='\r'?'\n':c);
                    }
                    break;
                case IN_STRING:
                    if (!parserState.isLastChar('\\') && c == '"') {
                        state = State.CODE;
                    }
                    break;
                case IN_CHAR:
                    if (!parserState.isLastChar('\\') && c == '\'') {
                        state = State.CODE;
                    }
                    break;
                default:
                    throw new RuntimeException("Unexpected");
            }
            switch (c){
                case '\n':
                case '\r':
                    currLine+=1;
                    currCol = 1;
                    break;
                case '\t':
                    currCol+=COLUMNS_PER_TAB;
                    break;
                default:
                    currCol+=1;
            }
            // ok we have two slashes in a row inside a string
            // we want to replace them with... anything else, to not confuse
            // the parser
            if (state==State.IN_STRING && parserState.isLastChar('\\') && c == '\\') {
                parserState.reset();
            } else {
                parserState.update(c);
            }
        }

        if (state==State.IN_LINE_COMMENT){
            currentLineComment.setContent(currentContent.toString());
            currentLineComment.setEndLine(currLine);
            currentLineComment.setEndColumn(currCol);
            comments.addComment(currentLineComment);
        }

        return comments;
    }

}
