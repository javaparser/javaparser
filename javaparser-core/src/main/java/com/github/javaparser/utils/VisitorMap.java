package com.github.javaparser.utils;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * A map that overrides the equals and hashcode calculation of the added nodes
 * by using another equals and hashcode visitor for those methods.
 */
public class VisitorMap<N extends Node, V> implements Map<N, V> {
    private final Map<EqualsHashcodeOverridingFacade, V> innerMap = new HashMap<>();
    private final GenericVisitor<Integer, Void> hashcodeVisitor;
    private final GenericVisitor<Boolean, Visitable> equalsVisitor;

    /**
     * Pass the visitors to use for equals and hashcode.
     */
    public VisitorMap(GenericVisitor<Integer, Void> hashcodeVisitor, GenericVisitor<Boolean, Visitable> equalsVisitor) {
        this.hashcodeVisitor = hashcodeVisitor;
        this.equalsVisitor = equalsVisitor;
    }
    
    @Override
    public int size() {
        return innerMap.size();
    }

    @Override
    public boolean isEmpty() {
        return innerMap.isEmpty();
    }

    @Override
    public boolean containsKey(Object key) {
        return innerMap.containsKey(new EqualsHashcodeOverridingFacade((N) key));
    }

    @Override
    public boolean containsValue(Object value) {
        return innerMap.containsValue(value);
    }

    @Override
    public V get(Object key) {
        return innerMap.get(new EqualsHashcodeOverridingFacade((N) key));
    }

    @Override
    public V put(N key, V value) {
        return innerMap.put(new EqualsHashcodeOverridingFacade(key), value);
    }

    private class EqualsHashcodeOverridingFacade implements Visitable {
        private final N overridden;

        EqualsHashcodeOverridingFacade(N overridden) {
            this.overridden = overridden;
        }

        @Override
        public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
            throw new AssertionError();
        }

        @Override
        public <A> void accept(VoidVisitor<A> v, A arg) {
            throw new AssertionError();
        }

        @Override
        public final int hashCode() {
            return overridden.accept(hashcodeVisitor, null);
        }

        @Override
        public boolean equals(final Object obj) {
            if (obj == null || !(obj instanceof VisitorMap.EqualsHashcodeOverridingFacade)) {
                return false;
            }
            return overridden.accept(equalsVisitor, ((EqualsHashcodeOverridingFacade) obj).overridden);
        }
    }

    @Override
    public V remove(Object key) {
        return innerMap.remove(new EqualsHashcodeOverridingFacade((N) key));
    }

    @Override
    public void putAll(Map<? extends N, ? extends V> m) {
        m.forEach(this::put);
    }

    @Override
    public void clear() {
        innerMap.clear();
    }

    @Override
    public Set<N> keySet() {
        return innerMap.keySet().stream()
                .map(k -> k.overridden)
                .collect(Collectors.toSet());
    }

    @Override
    public Collection<V> values() {
        return innerMap.values();
    }

    @Override
    public Set<Entry<N, V>> entrySet() {
        return innerMap.entrySet().stream()
                .map(e -> new HashMap.SimpleEntry<>(e.getKey().overridden, e.getValue()))
                .collect(Collectors.toSet());
    }
}
