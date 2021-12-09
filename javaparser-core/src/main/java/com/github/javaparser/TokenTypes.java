/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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

import com.github.javaparser.utils.LineSeparator;

import static com.github.javaparser.GeneratedJavaParserConstants.*;

/**
 * Complements GeneratedJavaParserConstants
 */
public class TokenTypes {
    public static boolean isWhitespace(int kind) {
        return getCategory(kind).isWhitespace();
    }

    public static boolean isEndOfLineToken(int kind) {
        return getCategory(kind).isEndOfLine();
    }

    public static boolean isWhitespaceOrComment(int kind) {
        return getCategory(kind).isWhitespaceOrComment();
    }

    /**
     * @deprecated Use {@link #isWhitespaceButNotEndOfLine(int)} which more explicitly reflects that this also includes
     * other whitespace e.g. {@code EOF} and {@code CTRL_Z} and a large number of other characters.
     * See the grammar for details of exactly which characters are included as a "space" (.
     * <pre>{@code
     *   <SPACE: [" ", "\t", "\f", "\u0085", "\u00A0", "\u1680", "\u180e", "\u2000", "\u2001", "\u2002", "\u2003", "\u2004", "\u2005",
     *       "\u2006", "\u2007", "\u2008", "\u2009", "\u200a", "\u200b", "\u200c", "\u200d", "\u2028", "\u2029", "\u202f", "\u205f", "\u2060", "\u3000", "\ufeff"]>
     *  }</pre>
     */
    @Deprecated
    public static boolean isSpaceOrTab(int kind) {
        return isWhitespaceButNotEndOfLine(kind);
    }

    public static boolean isWhitespaceButNotEndOfLine(int kind) {
        return getCategory(kind).isWhitespaceButNotEndOfLine();
    }

    public static boolean isComment(int kind) {
        return getCategory(kind).isComment();
    }

    /**
     * @return the kind of EOL token to use on the platform you're running on.
     */
    public static int eolTokenKind(LineSeparator lineSeparator) {
        if (lineSeparator.equalsString(LineSeparator.LF)) {
            return UNIX_EOL;
        }
        if (lineSeparator.equalsString(LineSeparator.CRLF)) {
            return WINDOWS_EOL;
        }
        if (lineSeparator.equalsString(LineSeparator.CR)) {
            return OLD_MAC_EOL;
        }
        throw new AssertionError("Unknown EOL character sequence");
    }

    public static int eolTokenKind() {
        return eolTokenKind(LineSeparator.SYSTEM);
    }

    /**
     * @return the token kind for a single space.
     */
    public static int spaceTokenKind() {
        return SPACE;
    }

    /**
     * Category of a token, a little more detailed than
     * <a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.5">The JLS</a>.
     */
    public static JavaToken.Category getCategory(int kind) {
        switch (kind) {
            case WINDOWS_EOL:
            case UNIX_EOL:
            case OLD_MAC_EOL:
                return JavaToken.Category.EOL;
            case JML_IGNORE_SINGLE_LINE_START:
            case EOF:
            case SPACE:
            case AT_AT_BEGINN:
            case CTRL_Z:
                return JavaToken.Category.WHITESPACE_NO_EOL;
            case SINGLE_LINE_COMMENT:
            case JAVADOC_COMMENT:
            case MULTI_LINE_COMMENT:
                return JavaToken.Category.COMMENT;
            case ABSTRACT:
            case AXIOM:
            case BEHAVIOUR:
            case BIGINT:
            case BIGINT_MATH:
            case BREAK_BEHAVIOR:
            case BREAK_BEHAVIOUR:
            case CALLABLE_REDUNDANTLY: //case BY:
            case DURATION:
            case CALLABLE:
            case CAPTURES:
            case CAPTURES_REDUNDANTLY:
            case CHOOSE:
            case CHOOSE_IF:
            case CONSTRAINT:
            case CONSTRAINT_REDUNDANTLY:
            case CONSTRUCTOR:
            case CONTINUE_BEHAVIOUR:
            case DECLASSIFIES:
            case DECREASES:
            case DECREASES_REDUNDANTLY:
            case DECREASING_REDUNDANTLY:
            case DURATION_REDUNDANTLY:
            case ELEMTYPE:
            case MODEL_BEHAVIOR:
            case MODEL_BEHAVIOUR:
            case ENSURES_REDUNDANTLY:
            case ERASES:
            case EXAMPLE:
            case EXCEPTIONAL_EXAMPLE:
            case EXSURES:
            case EXSURES_REDUNDANTLY:
            case EXTRACT:
            case FIELD:
                //case FRESH:
            case HELPER:
            case INITIALIZER:
            case INITIALLY:
            case INSTANCE:
                //case INTO:
            case INVARIANT_REDUNDANTLY:
                //case INVARIANT_FOR:
            case IN_REDUNDANTLY:
                //case IS_INITIALIZED:
            case JAVA_MATH:
                //case LBLNEG:
                //case LBLPOS:
            case MAINTAINING_REDUNDANTLY:
            case MAPS:
            case MAPS_REDUNDANTLY:
            case MODEL_PROGRAM:
            case MODIFIES:
            case MONITORED:
            case MONITORS_FOR:
            case JML_BLOCK_COMMENT:
            case JML_LINE_COMMENT:
            //case NONNULLELEMENTS:
            case NON_NULL:
                //case NOT_SPECIFIED:
            /*case ONLY_ACCESSED:
            case ONLY_ASSIGNED:
            case ONLY_CALLED:
            case ONLY_CAPTURED:*/
            case OR:
            case PRODUCT:
            //case REACH:
            case READABLE:
            case LOOP_INVARIANT_FREE:
            //case REAL:
            case REFINING:
            case REQUIRES_REDUNDANTLY:
            case RETURN_BEHAVIOUR:
                //case SPACE_ESC:
            case SPEC_SAFE_MATH:
            case STATIC_INITIALIZER:
            case SUBTYPE:
            case TYPE:
            //case TYPEOF:
            case UNINITIALIZED:
            case WRITABLE:
                //case NEW_OBJECTS:
                //case INFINITE_UNION:
            case ASSERT:
            case BOOLEAN:
            case BREAK:
            case BYTE:
            case CASE:
            case CATCH:
            case CHAR:
            case CLASS:
            case CONST:
            case CONTINUE:
            case _DEFAULT:
            case DO:
            case DOUBLE:
            case ELSE:
            case ENUM:
            case EXTENDS:
            case FINAL:
            case FINALLY:
            case FLOAT:
            case FOR:
            case GOTO:
            case IF:
            case IMPLEMENTS:
            case IMPORT:
            case INSTANCEOF:
            case INT:
            case INTERFACE:
            case LONG:
            case NATIVE:
            case NEW:
            case PACKAGE:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
            case RECORD:
            case RETURN:
            case SHORT:
            case STATIC:
            case STRICTFP:
            case SUPER:
            case SWITCH:
            case SYNCHRONIZED:
            case THIS:
                //case STOREREF:
            case THROW:
            case THROWS:
            case TRANSIENT:
            case TRY:
            case RESULT:
            case LOOP_CONTRACT:
            case LOOP_INVARIANT:
            case LOOP_INVARIANT_REDUNDANTLY:
            case MAINTAINING:
            case DECREASING:
            case VOID:
            case VOLATILE:
            case WHILE:
            case YIELD:
            case REQUIRES:
            case TO:
            case WITH:
            case OPEN:
            case OPENS:
            case USES:
            case MODULE:
            case EXPORTS:
            case PROVIDES:
            case TRANSITIVE:
            case INVARIANT:
            case ACCESSIBLE:
            case ENSURES:
            case NORMAL_BEHAVIOR:
            case EXCEPTIONAL_BEHAVIOR:
            case BEHAVIOR:
            case CONTINUE_BEHAVIOR:
            case BREAKS:
            case ENSURES_FREE:
            case REQUIRES_FREE:
            case CONTINUES:
            case FORALL:
            case FOR_EXAMPLE:
            case FORALLQ:
            case HENCE_BY_REDUNDANTLY:
            case HENCE_BY:
            case ASSERT_REDUNDANTLY:
            case ASSUME_REDUNDANTLY:
            case ASSIGNABLE:
            case ASSIGNABLE_REDUNDANTLY:
            case REPRESENTS:
            case REPRESENTS_REDUNDANTLY:
            case ACCESSIBLE_REDUNDANTLY:
            case OLD:
                //case OLD_ESC:
            case PRE_ESC:
            case PRE:
            case PRE_REDUNDANTLY:
            case POST:
            case POST_REDUNDANTLY:
            case ABRUPT_BEHAVIOR:
            case ABRUPT_BEHAVIOUR:
            case NORMAL_BEHAVIOUR:
            case BREAKS_REDUNDANTLY:
            case CONTINUES_REDUNDANTLY:
            case EXCEPTIONAL_BEHAVIOUR:
                //case SINGLETON:
                //case LOCKSET:
//            case LOCSET:
//            case UNION:
//            case INTERSECT:
//            case SUBSET:
//            case DISJOINT:
//            case SETMINUS:
            case NEW_OBJECT:
                //case NEWELEMSFRESH:
                //case EMPTYSET:
                //case NOT_ASSIGNED:
                //case NOT_MODIFIED:
                //case NOTHING:
            case STRICTLY_PURE:
            case PURE:
                //case STRICTLY_NOTHING:
                //case EVERYTHING:
            case DIVERGES:
            case DIVERGES_REDUNDANTLY:
            case WORKING_SPACE:
            case WORKING_SPACE_ESC:
            case WORKING_SPACE_REDUNDANTLY:
            case SIGNALS_ONLY:
            case SIGNALS_ONLY_REDUNDANTLY:
            case SIGNALS_REDUNDANTLY:
            case SIGNALS:
            case ESC_MEASURED_BY:
            case MEASURED_BY:
            case MEASURED_BY_REDUNDANTLY:
            case MODEL:
            case MODIFIABLE:
            case MODIFIABLE_REDUNDANTLY:
            case MODIFIES_REDUNDANTLY:
            case RETURNS_REDUNDANTLY:
            case RETURNS:
            case RETURN_BEHAVIOR:
                //case SAME:
            case SET:
            case SAFE_MATH:
            case CODE:
            case CODE_BIGINT_MATH:
            case CODE_JAVA_MATH:
            case CODE_SAFE_MATH:
            case SPEC_PACKAGE:
            case SPEC_PRIVATE:
            case SPEC_BIGINT_MATH:
            case SPEC_PUBLIC:
            case SPEC_PROTECTED:
            case SPEC_JAVA_MATH:
            case SUM:
            case EXISTS:
            case NULLABLE:
            case NULLABLE_BY_DEFAULT:
            case NUM_OF:
            case MIN:
            case MAX:
            case WARN:
            case WARN_OP:
            case NOWARN:
            case NOWARN_OP:
            case GHOST:
            case WHEN:
            case WHEN_REDUNDANTLY:
                //case STATIC_INVARIANT_FOR:
            case SUCH_THAT:
            case ALSO:
            case NESTED_CONTRACT_END:
            case NESTED_CONTRACT_START:
            case ASSUME:
            case IN:
            case IMPLIES_THAT:
            case JML_IDENTIFIER:
            case METHOD:
            case DETERMINES:
            case UNREACHABLE:
            case NORMAL_EXAMPLE:
            case TWO_STATE:
            case NON_NULL_BY_DEFAULT:
            case NO_STATE:
            case LOOP_MODIFIES:
            case NONNULLELEMENTS:
                return JavaToken.Category.KEYWORD;
            case LONG_LITERAL:
            case INTEGER_LITERAL:
            case DECIMAL_LITERAL:
            case HEX_LITERAL:
            case OCTAL_LITERAL:
            case BINARY_LITERAL:
            case FLOATING_POINT_LITERAL:
            case DECIMAL_FLOATING_POINT_LITERAL:
            case DECIMAL_EXPONENT:
            case HEXADECIMAL_FLOATING_POINT_LITERAL:
            case HEXADECIMAL_EXPONENT:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case TEXT_BLOCK_LITERAL:
            case TRUE:
            case FALSE:
            case NULL:
                return JavaToken.Category.LITERAL;
            case IDENTIFIER:
                return JavaToken.Category.IDENTIFIER;
            case LPAREN:
            case RPAREN:
            case LBRACE:
            case RBRACE:
            case LBRACKET:
            case RBRACKET:
            case SEMICOLON:
            case COMMA:
            case DOT:
            case DOTDOT:
            case ELLIPSIS:
            case AT:
            case DOUBLECOLON:
                return JavaToken.Category.SEPARATOR;
            case EQUIVALENCE:
            case UNKNOWN_OP:
            case UNKNOWN_OP_EQ:
            case ANTIVALENCE:
            case ASSIGN:
            case LT:
            case BANG:
            case TILDE:
            case HOOK:
            case COLON:
            case EQ:
            case LE:
            case GE:
            case NE:
            case SC_OR:
            case SC_AND:
            case INCR:
            case DECR:
            case PLUS:
            case MINUS:
            case STAR:
            case SLASH:
            case BIT_AND:
            case BIT_OR:
            case XOR:
            case REM:
            case LSHIFT:
            case PLUSASSIGN:
            case MINUSASSIGN:
            case STARASSIGN:
            case SLASHASSIGN:
            case ANDASSIGN:
            case ORASSIGN:
            case XORASSIGN:
            case REMASSIGN:
            case LSHIFTASSIGN:
            case RSIGNEDSHIFTASSIGN:
            case RUNSIGNEDSHIFTASSIGN:
            case ARROW:
            case RUNSIGNEDSHIFT:
            case RSIGNEDSHIFT:
            case IMPLICATION:
            case IMPLICATION_BACKWARD:
            case GT:
                return JavaToken.Category.OPERATOR;
            // The following are tokens that are only used internally by the lexer
            case ENTER_JAVADOC_COMMENT:
            case ENTER_MULTILINE_COMMENT:
            case COMMENT_CONTENT:
            case HEX_DIGITS:
            case LETTER:
            case UNICODE_ESCAPE:
            case PART_LETTER:
            case TEXT_BLOCK_CONTENT:
            case ENTER_TEXT_BLOCK:
                throw new IllegalArgumentException("Internal token kind given " + kind);
            default:
                throw new AssertionError("Unable to categorise token kind " + kind + " -- has it recently been added to the grammar but not classified within TokenTypes.java, perhaps?");
        }
    }
}
