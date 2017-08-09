package com.github.javaparser;

import java.util.Optional;
import java.util.function.Predicate;

public class TokenCursor {
    private Optional<JavaToken> token;

    public TokenCursor(JavaToken token) {
        this.token = Optional.of(token);
    }

    public TokenCursor endKey() {
        return this;
    }

    public TokenCursor returnKey() {
        return this;
    }

    public TokenCursor indentLikePreviousLine() {
        return this;
    }

    public TokenCursor insert(JavaToken javaToken) {
        token.ifPresent(t -> {
            t.getPreviousToken().ifPresent(p -> {
                p.setNextToken(Optional.of(javaToken));
                javaToken.setPreviousToken(Optional.of(p));
            });
            t.setPreviousToken(Optional.of(javaToken));
            javaToken.setNextToken(Optional.of(t));
        });
        return previous();
    }

    public TokenCursor find(Predicate<JavaToken> matcher) {
        return this;
    }

    public TokenCursor findBackwards(Predicate<JavaToken> matcher) {
        return this;
    }

    public TokenCursor deleteToken() {
        token.ifPresent(t -> {
            final Optional<JavaToken> nextToken = t.getNextToken();
            final Optional<JavaToken> previousToken = t.getPreviousToken();

            previousToken.ifPresent(p -> p.setNextToken(nextToken));
            nextToken.ifPresent(n -> n.setPreviousToken(previousToken));
            
            token = nextToken;
        });
        return this;
    }

//    public TokenCursor replaceToken(Function<JavaToken, JavaToken> replacer) {
//        return this;
//    }

    public TokenCursor deleteWhitespace() {
        return this;
    }

    public TokenCursor next() {
        token = token.flatMap(JavaToken::getNextToken);
        return this;
    }

    public TokenCursor previous() {
        token = token.flatMap(JavaToken::getPreviousToken);
        return this;
    }
}


