package org.jfree.data.time;

public class MillisecondUser {

    void use(Millisecond millisecond) {
        millisecond.getMillisecond();
        millisecond.getEnd();
        millisecond.hashCode();
        acceptPeriod(millisecond);
        acceptString(millisecond);
        int month = Millisecond.JANUARY;
    }

    void acceptPeriod(RegularTimePeriod period) {}

    void acceptString(String s) {}
}
