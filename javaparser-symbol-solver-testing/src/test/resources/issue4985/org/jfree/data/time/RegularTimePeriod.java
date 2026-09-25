package org.jfree.data.time;

import java.util.Date;

// MonthConstants comes from a library that is not available to the type solver
import org.jfree.date.MonthConstants;

public abstract class RegularTimePeriod implements TimePeriod, Comparable, MonthConstants {

    protected long pegged;

    public abstract long getFirstMillisecond();

    public Date getStart() {
        return new Date(getFirstMillisecond());
    }

    public Date getEnd() {
        return new Date(getFirstMillisecond());
    }
}
