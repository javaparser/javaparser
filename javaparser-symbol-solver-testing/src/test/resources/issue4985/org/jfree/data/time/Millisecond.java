package org.jfree.data.time;

public class Millisecond extends RegularTimePeriod {

    public long getFirstMillisecond() {
        return pegged;
    }

    public int getMillisecond() {
        return 0;
    }

    public int compareTo(Object o) {
        return 0;
    }
}
