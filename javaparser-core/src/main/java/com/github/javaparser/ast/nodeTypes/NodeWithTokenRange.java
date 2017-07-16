package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.TokenRange;

import java.util.Optional;

/**
 * A node that has a Range, which is every Node.
 * 
 */
public interface NodeWithTokenRange<N> {
    Optional<TokenRange> getTokenRange();

    N setTokenRange(TokenRange range);
}
