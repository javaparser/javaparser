package com.github.javaparser.jml.impl;

import com.github.javaparser.jml.services.IJmlDetection;
import lombok.var;
import org.jetbrains.annotations.NotNull;

import java.util.Collections;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Pattern;

import static jml.JmlComment.*;

/**
 * @author Alexander Weigl
 * @version 1 (1/31/20)
 */
public class SimpleJmlDetection implements IJmlDetection {
    private static final Pattern JML_COMMENT_PATTERN
            = Pattern.compile("^\\s*(//|/[*])(([-+]\\w+)*)[@].*", Pattern.DOTALL);

    @Override
    public boolean isJmlComment(@NotNull String comment) {
        return getAnnotationKeys(comment) != null;
    }

    /**
     * @param comment
     * @return null if the given comment is non-jml, else a set with the annotation keys are returned.
     */
    @Override
    public Set<String> getAnnotationKeys(@NotNull String comment) {
        var m = JML_COMMENT_PATTERN.matcher(comment);
        if (m.matches()) {
            if (m.groupCount() >= 3 && !m.group(2).trim().isEmpty()) {
                Set<String> s = new TreeSet<>();
                var annotations = m.group(2);
                Pattern.compile("(?=[+-])").splitAsStream(annotations)
                        .filter(it -> !it.trim().isEmpty())
                        .forEach(s::add);
                return s;
            }
            return Collections.emptySet();
        }
        return null;
    }

    @Override
    public int getType(String comment) {
        /*KeyJmlLexer lexer = new KeyJmlLexer(CharStreams.fromString(comment));
        boolean onlyModifier = true;
        Token tok;
        do {
            tok = lexer.nextToken();
            switch (tok.getType()) {
                //Ignore case
                case KeyJmlLexer.WS:
                case KeyJmlLexer.WS_CONTRACT:
                case KeyJmlLexer.WS_CONTRACT_IGNORE:
                case KeyJmlLexer.JML_START:
                case KeyJmlLexer.JML_END:
                case KeyJmlLexer.EOF:
                    break;

                //CONTRACT
                case KeyJmlLexer.BEHAVIOR:
                case KeyJmlLexer.NORMAL_BEHAVIOR:
                case KeyJmlLexer.EXCEPTIONAL_BEHAVIOR:
                case KeyJmlLexer.MODEL_BEHAVIOR:
                    return JmlComment.TYPE_METHOD_CONTRACT;
                case KeyJmlLexer.BREAK_BEHAVIOR:
                case KeyJmlLexer.CONTINUE_BEHAVIOR:
                case KeyJmlLexer.RETURN_BEHAVIOR:
                    return JmlComment.TYPE_BLOCK_CONTRACT;

                case KeyJmlLexer.ASSERT_:
                    return JmlComment.TYPE_ASSERT;

                case KeyJmlLexer.MODEL:
                case KeyJmlLexer.MODEL_METHOD_AXIOM:
                    return JmlComment.TYPE_MODEL_FIELD; //TODO decide between field or method

                case KeyJmlLexer.INVARIANT:
                case KeyJmlLexer.CONSTRAINT:
                case KeyJmlLexer.INITIALLY:
                case KeyJmlLexer.AXIOM:
                    return JmlComment.TYPE_CLASS_INVARIANT;

                case KeyJmlLexer.GHOST:
                    return JmlComment.TYPE_GHOST_FIELD;
                case KeyJmlLexer.LOOP_INVARIANT:
                    return JmlComment.TYPE_LOOP_INVARIANT;

                case KeyJmlLexer.SET:
                    return JmlComment.TYPE_GHOST_SET;

                case KeyJmlLexer.PACKAGE:
                case KeyJmlLexer.PUBLIC:
                case KeyJmlLexer.PRIVATE:
                case KeyJmlLexer.PROTECTED:
                case KeyJmlLexer.STATIC:
                case KeyJmlLexer.NON_NULL:
                case KeyJmlLexer.NULLABLE:
                case KeyJmlLexer.PURE:
                case KeyJmlLexer.STRICTLY_PURE:
                case KeyJmlLexer.ABSTRACT:
                case KeyJmlLexer.UNREACHABLE:
                case KeyJmlLexer.HELPER:
                case KeyJmlLexer.NULLABLE_BY_DEFAULT:
                case KeyJmlLexer.INSTANCE:
                case KeyJmlLexer.NO_STATE:
                case KeyJmlLexer.TWO_STATE:
                    break;
                default:
                    onlyModifier = false;
            }
        } while (tok.getType() != Token.EOF);

        if (onlyModifier)
            return JmlComment.TYPE_MODIFIER;
        */
        return JmlComment.TYPE_UNKNOWN;
    }

    @Override
    public int getAttachingType(@NotNull String comment, int type) {
        switch (type) {
            case TYPE_ASSERT:
            case TYPE_ASSUME:
            case TYPE_GHOST_SET:
                return AT_NEXT_STATEMENT;
            case TYPE_BLOCK_CONTRACT:
                return AT_NEXT_BLOCK;
            case TYPE_LOOP_INVARIANT:
                return AT_NEXT_LOOP;
            case TYPE_GHOST_FIELD:
            case TYPE_MODEL_METHOD:
            case TYPE_CLASS_INVARIANT:
                return AT_CONTAINING_TYPE;
            case TYPE_MODEL_FIELD:
                return AT_NEXT_FIELD;
            case TYPE_MODIFIER:
                return AT_NEXT_DECLARATION;
            case TYPE_METHOD_CONTRACT:
                return AT_NEXT_METHOD;
            case TYPE_UNKNOWN:
                return AT_UNKNOWN;
        }
        return 0;
    }
}
