package japa.parser.ast.comments;

import java.io.*;
import java.nio.charset.Charset;
import java.util.*;

/**
 * This parser cares exclusively about comments.
 */
public class CommentsParser {

    private enum State {
        CODE,
        WAITING_FOR_LINE_COMMENT,
        IN_LINE_COMMENT,
        WAITING_FOR_BLOCK_COMMENT,
        IN_BLOCK_COMMENT,
        WAITING_TO_LEAVE_BLOCK_COMMENT,
        IN_STRING;
    }

    private static final int COLUMNS_PER_TAB = 4;

    public CommentsCollection parse(final String source) throws IOException, UnsupportedEncodingException {
        InputStream in = new ByteArrayInputStream(source.getBytes(Charset.defaultCharset()));
        return parse(in, Charset.defaultCharset().name());
    }

    public CommentsCollection parse(final InputStream in, final String charsetName) throws IOException, UnsupportedEncodingException {
        boolean lastWasASlashR = false;
        BufferedReader br = new BufferedReader(new InputStreamReader(in, charsetName));
        CommentsCollection comments = new CommentsCollection();
        int r;

        Deque prevTwoChars = new LinkedList<Character>(Arrays.asList('z','z'));

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
                    if (prevTwoChars.peekLast().equals('/') && c == '/') {
                        currentLineComment = new LineComment();
                        currentLineComment.setBeginLine(currLine);
                        currentLineComment.setBeginColumn(currCol - 1);
                        state = State.IN_LINE_COMMENT;
                        currentContent = new StringBuffer();
                    } else if (prevTwoChars.peekLast().equals('/') && c == '*') {
                        currentBlockComment = new BlockComment();
                        currentBlockComment.setBeginLine(currLine);
                        currentBlockComment.setBeginColumn(currCol - 1);
                        state = State.IN_BLOCK_COMMENT;
                        currentContent = new StringBuffer();
                    } else if (c == '"') {
                        state = State.IN_STRING;
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
                    if (prevTwoChars.peekLast().equals('*') && c=='/' && !prevTwoChars.peekFirst().equals('/')){

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
                    if (!prevTwoChars.peekLast().equals('\\') && c == '"') {
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
            prevTwoChars.remove();
            prevTwoChars.add(c);
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
