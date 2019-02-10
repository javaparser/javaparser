package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.Position;
import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;

import java.util.Optional;

/**
 * A node that has a Range, which is every Node.
 * 
 */
public interface NodeWithRange<N> {
    Optional<Range> getRange();

    N setRange(Range range);

    /**
     * The begin position of this node in the source file.
     */
    default Optional<Position> getBegin() {
        return getRange().map(r -> r.begin);
    }

    /**
     * The end position of this node in the source file.
     */
    default Optional<Position> getEnd() {
        return getRange().map(r -> r.end);
    }

    default boolean containsWithin(Node other) {
        if (getRange().isPresent() && other.getRange().isPresent()) {
            return getRange().get().contains(other.getRange().get());
        }
        return false;
    }
}
