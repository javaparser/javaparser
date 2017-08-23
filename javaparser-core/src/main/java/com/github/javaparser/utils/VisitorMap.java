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
 * A facade for another java.util.Map that overrides the equals and hashcode calculation of the added nodes
 * by using another visitor for those methods.
 */
public class VisitorMap<N extends Node, V> implements Map<N, V> {
    // Cheat generics by removing them
    private final Map innerMap;
    private final GenericVisitor<Integer, Void> hashcodeVisitor;
    private final GenericVisitor<Boolean, Visitable> equalsVisitor;

    /**
     * Wrap a map and use different visitors for equals and hashcode.
     */
    public VisitorMap(Map<N, V> innerMap, GenericVisitor<Integer, Void> hashcodeVisitor, GenericVisitor<Boolean, Visitable> equalsVisitor) {
        this.innerMap = innerMap;
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
        return innerMap.containsKey(key);
    }

    @Override
    public boolean containsValue(Object value) {
        return innerMap.containsValue(value);
    }

    @Override
    public V get(Object key) {
        return (V) innerMap.get(key);
    }

    @Override
    public V put(N key, V value) {
        return (V) innerMap.put(new EqualsHashcodeOverridingFacade(key), value);
    }

    private class EqualsHashcodeOverridingFacade implements Visitable {
        private final N overridden;

        public EqualsHashcodeOverridingFacade(N overridden) {
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
        return (V) innerMap.remove(key);
    }

    @Override
    public void putAll(Map<? extends N, ? extends V> m) {
        innerMap.putAll(m);
    }

    @Override
    public void clear() {
        innerMap.clear();
    }

    @Override
    public Set<N> keySet() {
        return ((Map<EqualsHashcodeOverridingFacade, V>) innerMap).keySet().stream()
                .map(k -> k.overridden)
                .collect(Collectors.toSet());
    }

    @Override
    public Collection<V> values() {
        return innerMap.values();
    }

    @Override
    public Set<Entry<N, V>> entrySet() {
        return ((Map<EqualsHashcodeOverridingFacade, V>) innerMap).entrySet().stream()
                .map(e -> new HashMap.SimpleEntry<N, V>(e.getKey().overridden, e.getValue()))
                .collect(Collectors.toSet());
    }
}
