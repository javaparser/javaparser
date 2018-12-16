package com.github.javaparser.printer.lexicalpreservation;

import java.util.Iterator;

public class WrappingRangeIterator implements Iterator<Integer> {
    private final int limit;
    private int currentValue = 0;

    public WrappingRangeIterator(int limit) {
        this.limit = limit;
    }

    @Override
    public boolean hasNext() {
        return true;
    }

    @Override
    public Integer next() {
        int valueToReturn = currentValue;
        ++currentValue;
        if (currentValue == limit) {
            currentValue = 0;
        }
        return valueToReturn;
    }
}
