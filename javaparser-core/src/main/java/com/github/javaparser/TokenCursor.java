package com.github.javaparser;

import java.util.Optional;
import java.util.function.Function;
import java.util.function.Predicate;

import static com.github.javaparser.TokenTypes.eolToken;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A cursor that can examine and manipulate the token list.
 * <p>Note 1: it does not automatically update the AST!</p>
 * <p>Note 2: all of these methods fail silently. The usual error condition is "we ran off the list and now the cursor
 * is pointing nowhere" which can be checked with the valid() method.<p/>
 */
public class TokenCursor {
    private Optional<JavaToken> token;

    public TokenCursor(JavaToken token) {
        this.token = Optional.of(token);
    }

    /**
     * @return a copy of the cursor.
     */
    public TokenCursor clone() {
        return new TokenCursor(token.orElse(null));
    }

    /**
     * Like pressing enter: a new line is started with the current token at the beginning of it.
     * The cursor is now at this token at the beginning.
     */
    public TokenCursor newLine() {
        return insert(eolToken());
    }

    /**
     * Inserts newToken at the cursor, moving the current token forward.
     * Cursor stays at current token.
     */
    public TokenCursor insert(JavaToken newToken) {
        assertNotNull(newToken);
        token.ifPresent(t -> t.insert(newToken));
        return this;
    }

    /**
     * Inserts newToken at the cursor, moving the current token forward.
     * Cursor stays at current token.
     */
    public TokenCursor insertAfter(JavaToken newToken) {
        assertNotNull(newToken);
        token.ifPresent(t -> t.insertAfter(newToken));
        return this;
    }

    /**
     * Finds the token that matches "matcher".
     * If the current token matches, it returns immediately.
     * Otherwise it will look forward, to the end of the token list, until it finds a token that matches.
     * If it goes past the end of the list, the cursor is set to empty.
     */
    public TokenCursor find(Predicate<JavaToken> matcher) {
        assertNotNull(matcher);
        while (token.map(t -> !matcher.test(t)).orElse(false)) {
            token = token.get().getNextToken();
        }
        return this;
    }

    /**
     * Like "find" but does not look at the current token.
     */
    public TokenCursor findNext(Predicate<JavaToken> matcher) {
        assertNotNull(matcher);
        return toNextToken().find(matcher);
    }

    /**
     * Finds the token that matches "matcher".
     * If the current token matches, it returns immediately.
     * Otherwise it will look backward, to the start of the token list, until it finds a token that matches.
     * If it goes past the start of the list, the cursor is set to empty.
     */
    public TokenCursor findBackwards(Predicate<JavaToken> matcher) {
        assertNotNull(matcher);
        while (token.map(t -> !matcher.test(t)).orElse(false)) {
            token = token.get().getPreviousToken();
        }
        return this;
    }

    /**
     * Like "findBackwards" but does not look at the current token.
     */
    public TokenCursor findNextBackwards(Predicate<JavaToken> matcher) {
        assertNotNull(matcher);
        return toPreviousToken().findBackwards(matcher);
    }

    /**
     * Links the tokens around the current token together, making the current token disappear from the list.
     * The current token is forgotten, and the cursor now points at the token that followed it.
     */
    public TokenCursor deleteToken() {
        token.ifPresent(t -> {
            final Optional<JavaToken> nextToken = t.getNextToken();
            t.deleteToken();
            token = nextToken;
        });
        return this;
    }

    /**
     * Replaces the current token with newToken.
     * The cursor is now at newToken.
     */
    public TokenCursor replaceToken(JavaToken newToken) {
        assertNotNull(newToken);
        token.ifPresent(t -> t.replaceToken(newToken));
        token = Optional.of(newToken);
        return this;
    }

    /**
     * Replaces the current token with the result of replacer.
     * The cursor is now at newToken.
     */
    public TokenCursor replaceToken(Function<JavaToken, JavaToken> replacer) {
        assertNotNull(replacer);
        token.ifPresent(t -> replaceToken(replacer.apply(t)));
        return this;
    }

//    public TokenCursor deleteWhitespace() {
//        return this;
//    }

    /**
     * Moves the cursor forward to the next token in the list.
     * If it moves over the last token, the cursor is set to empty.
     */
    public TokenCursor toNextToken() {
        token = token.flatMap(JavaToken::getNextToken);
        return this;
    }

    /**
     * Moves the cursor backward to the previous token in the list.
     * If it moves over the first token, the cursor is set to empty.
     */
    public TokenCursor toPreviousToken() {
        token = token.flatMap(JavaToken::getPreviousToken);
        return this;
    }

    /**
     * Move the cursor to the first token in the token list.
     */
    public TokenCursor toFirstToken() {
        token = token.map(JavaToken::findFirstToken);
        return this;
    }

    /**
     * Move the cursor to the last token in the token list.
     */
    public TokenCursor toLastToken() {
        token = token.map(JavaToken::findLastToken);
        return this;
    }

    /**
     * Moves the cursor back until it finds an end of line character, then positions the cursor just after it.
     */
    public TokenCursor toStartOfLine() {
        return findNextBackwards(t -> t.getCategory().isEndOfLine()).toNextToken();
    }

    public TokenCursor toEndOfLine() {
        return find(t -> t.getCategory().isEndOfLine());
    }

    public TokenCursor insert(int tokenKind, String text) {
        assertNotNull(text);
        return insert(new JavaToken(tokenKind, text));
    }

    public boolean valid() {
        return token.isPresent();
    }

    public Optional<JavaToken> getToken() {
        return token;
    }

    @Override
    public String toString() {
        return token.map(JavaToken::toString).orElse("INVALID");
    }
}


