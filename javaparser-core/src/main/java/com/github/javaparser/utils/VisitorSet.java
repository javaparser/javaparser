/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.utils;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.stream.Collectors;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * A set that overrides the equals and hashcode calculation of the added nodes
 * by using another equals and hashcode visitor for those methods.
 */
public class VisitorSet<N extends Node> implements Set<N> {

    private final Set<EqualsHashcodeOverridingFacade> innerSet = new HashSet<>();
    private final GenericVisitor<Integer, Void> hashcodeVisitor;
    private final GenericVisitor<Boolean, Visitable> equalsVisitor;

    /**
     * Pass the visitors to use for equals and hashcode.
     */
    public VisitorSet(GenericVisitor<Integer, Void> hashcodeVisitor, GenericVisitor<Boolean, Visitable> equalsVisitor) {
        this.hashcodeVisitor = hashcodeVisitor;
        this.equalsVisitor = equalsVisitor;
    }

    @Override
    public boolean add(N elem) {
        return innerSet.add(new EqualsHashcodeOverridingFacade(elem));
    }

    @Override
    public boolean addAll(Collection<? extends N> col) {
        boolean modified = false;
        for (N elem : col)
            if (add(elem))
                modified = true;
        return modified;
    }

    @Override
    public void clear() {
        innerSet.clear();
    }

    @Override
    public boolean contains(Object elem) {
        return innerSet.contains(new EqualsHashcodeOverridingFacade((N) elem));
    }

    @Override
    public boolean containsAll(Collection<?> col) {
        for (Object elem : col)
            if (!contains(elem))
                return false;
        return true;
    }

    @Override
    public boolean isEmpty() {
        return innerSet.isEmpty();
    }

    @Override
    public Iterator<N> iterator() {
        return new Iterator<N>() {
            final Iterator<EqualsHashcodeOverridingFacade> itr = innerSet.iterator();

            @Override
            public boolean hasNext() {
                return itr.hasNext();
            }

            @Override
            public N next() {
                return itr.next().overridden;
            }

            @Override
            public void remove() {
                itr.remove();
            }
        };
    }

    @Override
    public boolean remove(Object elem) {
        return innerSet.remove(new EqualsHashcodeOverridingFacade((N) elem));
    }

    @Override
    public boolean removeAll(Collection<?> col) {
        boolean modified = false;
        for (Object elem : col)
            if (remove(elem))
                modified = true;
        return modified;
    }

    @Override
    public boolean retainAll(Collection<?> col) {
        int oldSize = size();
        clear();
        addAll((Collection<? extends N>) col);
        return size() != oldSize;
    }

    @Override
    public int size() {
        return innerSet.size();
    }

    @Override
    public Object[] toArray() {
        return innerSet.stream().map(facade -> facade.overridden).collect(Collectors.toList()).toArray();
    }

    @Override
    public <T> T[] toArray(T[] arr) {
        return innerSet.stream().map(facade -> facade.overridden).collect(Collectors.toList()).toArray(arr);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("[");
        if (size() == 0)
            return sb.append("]").toString();
        for (EqualsHashcodeOverridingFacade facade : innerSet) {
            sb.append(facade.overridden.toString() + ",");
        }
        return sb.replace(sb.length() - 2, sb.length(), "]").toString();
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
            if (obj == null || !(obj instanceof VisitorSet.EqualsHashcodeOverridingFacade)) {
                return false;
            }
            return overridden.accept(equalsVisitor, ((EqualsHashcodeOverridingFacade) obj).overridden);
        }
    }

}
