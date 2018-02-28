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

    /**
     * @return true if other's range is not outside of this node's range.
     */
    default boolean containsWithin(Node other) {
        if (getRange().isPresent() && other.getRange().isPresent()) {
            return getRange().get().contains(other.getRange().get());
        }
        return false;
    }

    /**
     * @deprecated use isAfter() on range
     */
    @Deprecated
    default boolean isPositionedAfter(Position position) {
        return getRange().map(r -> r.isAfter(position)).orElse(false);
    }

    /**
     * @deprecated use isBefore() on range
     */
    @Deprecated
    default boolean isPositionedBefore(Position position) {
        return getRange().map(r -> r.isBefore(position)).orElse(false);
    }
}
