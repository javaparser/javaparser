package com.github.javaparser.jml;

import com.github.javaparser.JavaToken;
import com.github.javaparser.Position;
import com.github.javaparser.Range;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.jml.doc.JmlDoc;

import java.util.Optional;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (11/23/21)
 */
public class JmlDocSanitizer {
    private final Set<String> enabledKeys;

    public JmlDocSanitizer(Set<String> enabledKeys) {
        this.enabledKeys = enabledKeys;
    }

    public String asString(NodeList<JmlDoc> jmlDocs) {
        if (jmlDocs.isEmpty()) return "";
        StringBuilder s = new StringBuilder(1024);
        Position last = new Position(0, 0);

        for (JmlDoc jmlDoc : jmlDocs) {
            JavaToken tok = jmlDoc.getContent();
            final Optional<Range> range = tok.getRange();
            if (range.isPresent()) {
                Position cur = range.get().begin;
                if (last.line < cur.line) {
                    for (int i = last.line; i < cur.line; i++) {
                        s.append("\n");
                    }
                    for (int i = 0; i < cur.column; i++) {
                        s.append(" ");
                    }
                    last = cur;
                }
            }
            s.append(jmlDoc.getContent().getText());
        }

        cleanComments(s);
        cleanAtSigns(s);
        return s.toString();
    }

    private void cleanAtSigns(StringBuilder s) {
        for (int pos = 0; pos < s.length(); pos++) {
            char cur = s.charAt(pos);
            if (cur == '\n') {
                ++pos;
                for (; pos < s.length(); pos++) {
                    if (!Character.isWhitespace(s.charAt(pos)))
                        break;
                }
                for (; pos < s.length(); pos++) {
                    if ('@' == s.charAt(pos)) {
                        s.setCharAt(pos, ' ');
                    }
                }
            }
        }
    }

    private void cleanComments(StringBuilder s) {
        int cur = 0;
        for (; cur < s.length() - 1; ++cur) {
            if (isJavaCommentStart(s, cur)) {
                if (isJmlComment(s, cur)) {
                    cur = activateJmlComment(s, cur);
                } else {
                    cur = cleanComment(s, cur);
                }
            }
        }
    }

    private int cleanComment(StringBuilder s, int pos) {
        char second = s.charAt(pos + 1);
        int end;
        if (second == '*') {
            end = s.indexOf("*/", pos + 2);
        } else {
            end = s.indexOf("\n", pos + 2);
        }
        if (end == -1) { // Comment is aborted by EOF rather than */ or \n
            end = s.length();
        }

        for (int i = pos; i < end; i++) {
            s.setCharAt(i, ' ');
        }
        return end;
    }

    private int activateJmlComment(StringBuilder s, int pos) {
        boolean blockComment = s.charAt(pos) == '/' && s.charAt(pos + 1) == '*';
        if (blockComment) {
            int endPos = s.indexOf("*/", pos);
            if (endPos >= 0) {
                s.setCharAt(endPos, ' ');
                s.setCharAt(endPos + 1, ' ');
            }
        }
        for (int i = pos; i < s.length(); i++) {
            char point = s.charAt(i);
            s.setCharAt(i, ' ');
            if (point == '@') {
                return i;
            }
        }
        return s.length();
    }

    private boolean isJmlComment(StringBuilder s, int pos) {
        int posAt = s.indexOf("@", pos + 2);
        if (posAt < 0) return false;
        for (int i = pos + 2; i < posAt; i++) {
            int point = s.charAt(i);
            if (!(Character.isJavaIdentifierPart(point) || point == '-' || point == '+')) {
                return false;
            }
        }

        if (pos + 2 == posAt) //unconditonal JML comment
            return true;

        String[] keys = s.substring(pos + 2, posAt).split("[+-]");
        return isActiveJmlSpec(keys);

        /*for (int i = pos + 2; i < s.length() ; i++) {
            if()
            else if (Character.isJavaIdentifierPart(point) || point == '-' || point == '+') {
        }*/
    }


    private boolean isJavaCommentStart(StringBuilder s, int pos) {
        return s.charAt(pos) == '/' && (s.charAt(pos + 1) == '*' || s.charAt(pos + 1) == '/');
    }


    public boolean isActiveJmlSpec(String[] keys) {
        if (keys.length == 0) {
            //a JML annotation with no keys is always included,
            return true;
        }

        //a JML annotation with at least one positive-key is only included
        boolean plusKeyFound = false;
        //if at least one of these positive keys is enabled
        boolean enabledPlusKeyFound = false;

        //a JML annotation with an enabled negative-key is ignored (even if there are enabled positive-keys).
        boolean enabledNegativeKeyFound = false;

        for (String marker : keys) {
            if (marker.isEmpty()) continue;

            plusKeyFound = plusKeyFound || isPositive(marker);
            enabledPlusKeyFound = enabledPlusKeyFound || isPositive(marker) && isEnabled(marker);
            enabledNegativeKeyFound = enabledNegativeKeyFound || isNegative(marker) && isEnabled(marker);
            if ("-".equals(marker) || "+".equals(marker)) {
                return false;
            }
        }

        return (!plusKeyFound || enabledPlusKeyFound) && !enabledNegativeKeyFound;
    }

    private boolean isNegative(String marker) {
        return marker.charAt(0) == '-';
    }

    private boolean isEnabled(String marker) {
        // remove [+-] prefix
        return enabledKeys.contains(marker.substring(1).toLowerCase());
    }

    private boolean isPositive(String marker) {
        return marker.charAt(0) == '+';
    }
}

