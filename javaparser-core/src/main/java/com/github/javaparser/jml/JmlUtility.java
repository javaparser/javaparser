package com.github.javaparser.jml;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.jml.NodeWithContracts;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.clauses.JmlSignalsClause;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.quality.Preconditions;
import com.github.javaparser.resolution.types.ResolvedType;
import java.util.*;
import java.util.function.Consumer;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;
import org.jetbrains.annotations.NotNull;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.22)
 */
public class JmlUtility {

    public static void fixRangeContracts(@NotNull NodeWithContracts<? extends Node> n) {
        Preconditions.checkNotNull(n, "Parameter n can't be null.");
        Optional<JmlContract> first;
        var m = ((Node) n);
        var r = m.getRange();
        if (r.isPresent()
                && (first = n.getContracts().getFirst()).isPresent()
                && first.get().getRange().isPresent()) {
            m.setRange(r.get().withBegin(first.get().getRange().get().begin));
        }
    }

    public static ResolvedType resolveException(JmlSignalsClause n) {
        var jle = new ClassOrInterfaceType("java.lang.Exception");
        var rjle = n.getSymbolResolver().toResolvedType(jle, ResolvedType.class);
        return rjle;
    }

    public static Stream<Node> getAllNodes(Node node) {
        return StreamSupport.stream(new NodeSpliterator(node), false);
    }
}

class NodeSpliterator implements Spliterator<Node> {

    private final Queue<Node> toExplore = new LinkedList<>();

    private final Queue<Node> toSupply = new LinkedList<>();

    public NodeSpliterator(Node node) {
        toExplore.add(node);
    }

    private void explore() {
        if (!toExplore.isEmpty()) {
            var n = toExplore.poll();
            toExplore.addAll(n.getChildNodes());
            toSupply.add(n);
        }
    }

    @Override
    public boolean tryAdvance(Consumer<? super Node> action) {
        if (toSupply.isEmpty()) {
            explore();
        }
        if (!toSupply.isEmpty()) {
            action.accept(toSupply.poll());
            return true;
        }
        return false;
    }

    @Override
    public Spliterator<Node> trySplit() {
        if (!toExplore.isEmpty()) {
            return new NodeSpliterator(toExplore.poll());
        }
        return null;
    }

    @Override
    public long estimateSize() {
        return 64;
    }

    @Override
    public int characteristics() {
        return Spliterator.NONNULL | Spliterator.IMMUTABLE;
    }
}

class NodeIterator implements Iterator<Node> {

    private final Queue<Node> toExplore = new LinkedList<>();

    private final Queue<Node> toSupply = new LinkedList<>();

    public NodeIterator(Node node) {
        toExplore.add(node);
    }

    @Override
    public Node next() {
        if (toSupply.isEmpty()) {
            explore();
        }
        if (!toSupply.isEmpty()) return toSupply.poll();
        throw new IllegalStateException("no more elements");
    }

    @Override
    public boolean hasNext() {
        return !toSupply.isEmpty() || !toExplore.isEmpty();
    }

    private void explore() {
        if (!toExplore.isEmpty()) {
            var n = toExplore.poll();
            toExplore.addAll(n.getChildNodes());
            toSupply.add(n);
        }
    }
}
