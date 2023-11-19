package com.github.javaparser.printer.lexicalpreservation;

import java.util.NoSuchElementException;

public interface LookaheadIterator<E> {

    /**
     * Returns the next element in iteration without advancing the underlying iterator.
     * If the iterator is already exhausted, null will be returned.
     * <p>
     * Note: this method does not throw a {@link NoSuchElementException} if the iterator
     * is already exhausted. If you want such a behavior, use {@link #element()} instead.
     * <p>
     * The rationale behind this is to follow the {@link java.util.Queue} interface
     * which uses the same terminology.
     *
     * @return the next element from the iterator
     */
    public E peek();

    /**
     * Returns the next element in iteration without advancing the underlying iterator.
     * If the iterator is already exhausted, null will be returned.
     *
     * @return the next element from the iterator
     * @throws NoSuchElementException if the iterator is already exhausted according to {@link #hasNext()}
     */
    public E element();
}
