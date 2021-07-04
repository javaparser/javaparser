/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.commons.math3.stat;

import java.io.Serializable;
import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.SortedMap;
import java.util.TreeMap;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.MathUtils;

/**
 * Maintains a frequency distribution.
 * <p>
 * Accepts int, long, char or Comparable values.  New values added must be
 * comparable to those that have been added, otherwise the add method will
 * throw an IllegalArgumentException.</p>
 * <p>
 * Integer values (int, long, Integer, Long) are not distinguished by type --
 * i.e. <code>addValue(Long.valueOf(2)), addValue(2), addValue(2l)</code> all have
 * the same effect (similarly for arguments to <code>getCount,</code> etc.).</p>
 * <p>NOTE: byte and short values will be implicitly converted to int values
 * by the compiler, thus there are no explicit overloaded methods for these
 * primitive types.</p>
 * <p>
 * char values are converted by <code>addValue</code> to Character instances.
 * As such, these values are not comparable to integral values, so attempts
 * to combine integral types with chars in a frequency distribution will fail.
 * </p>
 * <p>
 * Float is not coerced to Double.
 * Since they are not Comparable with each other the user must do any necessary coercion.
 * Float.NaN and Double.NaN are not treated specially; they may occur in input and will
 * occur in output if appropriate.
 * </b>
 * <p>
 * The values are ordered using the default (natural order), unless a
 * <code>Comparator</code> is supplied in the constructor.</p>
 *
 */
public class Frequency implements Serializable {

    /** Serializable version identifier */
    private static final long serialVersionUID = -3845586908418844111L;

    /** underlying collection */
    private final SortedMap<Comparable<?>, Long> freqTable;

    /**
     * Default constructor.
     */
    public Frequency() {
        freqTable = new TreeMap<Comparable<?>, Long>();
    }

    /**
     * Constructor allowing values Comparator to be specified.
     *
     * @param comparator Comparator used to order values
     */
    @SuppressWarnings("unchecked") // TODO is the cast OK?
    public Frequency(Comparator<?> comparator) {
        freqTable = new TreeMap<Comparable<?>, Long>((Comparator<? super Comparable<?>>) comparator);
    }

    /**
     * Return a string representation of this frequency distribution.
     *
     * @return a string representation.
     */
    @Override
    public String toString() {
        NumberFormat nf = NumberFormat.getPercentInstance();
        StringBuilder outBuffer = new StringBuilder();
        outBuffer.append("Value \t Freq. \t Pct. \t Cum Pct. \n");
        Iterator<Comparable<?>> iter = freqTable.keySet().iterator();
        while (iter.hasNext()) {
            Comparable<?> value = iter.next();
            outBuffer.append(value);
            outBuffer.append('\t');
            outBuffer.append(getCount(value));
            outBuffer.append('\t');
            outBuffer.append(nf.format(getPct(value)));
            outBuffer.append('\t');
            outBuffer.append(nf.format(getCumPct(value)));
            outBuffer.append('\n');
        }
        return outBuffer.toString();
    }

    /**
     * Adds 1 to the frequency count for v.
     * <p>
     * If other objects have already been added to this Frequency, v must
     * be comparable to those that have already been added.
     * </p>
     *
     * @param v the value to add.
     * @throws MathIllegalArgumentException if <code>v</code> is not comparable with previous entries
     */
    public void addValue(Comparable<?> v) throws MathIllegalArgumentException {
        incrementValue(v, 1);
    }

    /**
     * Adds 1 to the frequency count for v.
     *
     * @param v the value to add.
     * @throws MathIllegalArgumentException if the table contains entries not
     * comparable to Long
     */
    public void addValue(int v) throws MathIllegalArgumentException {
        addValue(Long.valueOf(v));
    }

    /**
     * Adds 1 to the frequency count for v.
     *
     * @param v the value to add.
     * @throws MathIllegalArgumentException if the table contains entries not
     * comparable to Long
     */
    public void addValue(long v) throws MathIllegalArgumentException {
        addValue(Long.valueOf(v));
    }

    /**
     * Adds 1 to the frequency count for v.
     *
     * @param v the value to add.
     * @throws MathIllegalArgumentException if the table contains entries not
     * comparable to Char
     */
    public void addValue(char v) throws MathIllegalArgumentException {
        addValue(Character.valueOf(v));
    }

    /**
     * Increments the frequency count for v.
     * <p>
     * If other objects have already been added to this Frequency, v must
     * be comparable to those that have already been added.
     * </p>
     *
     * @param v the value to add.
     * @param increment the amount by which the value should be incremented
     * @throws MathIllegalArgumentException if <code>v</code> is not comparable with previous entries
     * @since 3.1
     */
    public void incrementValue(Comparable<?> v, long increment) throws MathIllegalArgumentException {
        Comparable<?> obj = v;
        if (v instanceof Integer) {
            obj = Long.valueOf(((Integer) v).longValue());
        }
        try {
            Long count = freqTable.get(obj);
            if (count == null) {
                freqTable.put(obj, Long.valueOf(increment));
            } else {
                freqTable.put(obj, Long.valueOf(count.longValue() + increment));
            }
        } catch (ClassCastException ex) {
            //TreeMap will throw ClassCastException if v is not comparable
            throw new MathIllegalArgumentException(
                  LocalizedFormats.INSTANCES_NOT_COMPARABLE_TO_EXISTING_VALUES,
                  v.getClass().getName());
        }
    }

    /**
     * Increments the frequency count for v.
     * <p>
     * If other objects have already been added to this Frequency, v must
     * be comparable to those that have already been added.
     * </p>
     *
     * @param v the value to add.
     * @param increment the amount by which the value should be incremented
     * @throws MathIllegalArgumentException if the table contains entries not
     * comparable to Long
     * @since 3.3
     */
    public void incrementValue(int v, long increment) throws MathIllegalArgumentException {
        incrementValue(Long.valueOf(v), increment);
    }

    /**
     * Increments the frequency count for v.
     * <p>
     * If other objects have already been added to this Frequency, v must
     * be comparable to those that have already been added.
     * </p>
     *
     * @param v the value to add.
     * @param increment the amount by which the value should be incremented
     * @throws MathIllegalArgumentException if the table contains entries not
     * comparable to Long
     * @since 3.3
     */
    public void incrementValue(long v, long increment) throws MathIllegalArgumentException {
        incrementValue(Long.valueOf(v), increment);
    }

    /**
     * Increments the frequency count for v.
     * <p>
     * If other objects have already been added to this Frequency, v must
     * be comparable to those that have already been added.
     * </p>
     *
     * @param v the value to add.
     * @param increment the amount by which the value should be incremented
     * @throws MathIllegalArgumentException if the table contains entries not
     * comparable to Char
     * @since 3.3
     */
    public void incrementValue(char v, long increment) throws MathIllegalArgumentException {
        incrementValue(Character.valueOf(v), increment);
    }

    /** Clears the frequency table */
    public void clear() {
        freqTable.clear();
    }

    /**
     * Returns an Iterator over the set of values that have been added.
     * <p>
     * If added values are integral (i.e., integers, longs, Integers, or Longs),
     * they are converted to Longs when they are added, so the objects returned
     * by the Iterator will in this case be Longs.</p>
     *
     * @return values Iterator
     */
    public Iterator<Comparable<?>> valuesIterator() {
        return freqTable.keySet().iterator();
    }

    /**
     * Return an Iterator over the set of keys and values that have been added.
     * Using the entry set to iterate is more efficient in the case where you
     * need to access respective counts as well as values, since it doesn't
     * require a "get" for every key...the value is provided in the Map.Entry.
     * <p>
     * If added values are integral (i.e., integers, longs, Integers, or Longs),
     * they are converted to Longs when they are added, so the values of the
     * map entries returned by the Iterator will in this case be Longs.</p>
     *
     * @return entry set Iterator
     * @since 3.1
     */
    public Iterator<Map.Entry<Comparable<?>, Long>> entrySetIterator() {
        return freqTable.entrySet().iterator();
    }

    //-------------------------------------------------------------------------

    /**
     * Returns the sum of all frequencies.
     *
     * @return the total frequency count.
     */
    public long getSumFreq() {
        long result = 0;
        Iterator<Long> iterator = freqTable.values().iterator();
        while (iterator.hasNext())  {
            result += iterator.next().longValue();
        }
        return result;
    }

    /**
     * Returns the number of values equal to v.
     * Returns 0 if the value is not comparable.
     *
     * @param v the value to lookup.
     * @return the frequency of v.
     */
    public long getCount(Comparable<?> v) {
        if (v instanceof Integer) {
            return getCount(((Integer) v).longValue());
        }
        long result = 0;
        try {
            Long count =  freqTable.get(v);
            if (count != null) {
                result = count.longValue();
            }
        } catch (ClassCastException ex) { // NOPMD
            // ignore and return 0 -- ClassCastException will be thrown if value is not comparable
        }
        return result;
    }

    /**
     * Returns the number of values equal to v.
     *
     * @param v the value to lookup.
     * @return the frequency of v.
     */
    public long getCount(int v) {
        return getCount(Long.valueOf(v));
    }

    /**
     * Returns the number of values equal to v.
     *
     * @param v the value to lookup.
     * @return the frequency of v.
     */
    public long getCount(long v) {
        return getCount(Long.valueOf(v));
    }

    /**
     * Returns the number of values equal to v.
     *
     * @param v the value to lookup.
     * @return the frequency of v.
     */
    public long getCount(char v) {
        return getCount(Character.valueOf(v));
    }

    /**
     * Returns the number of values in the frequency table.
     *
     * @return the number of unique values that have been added to the frequency table.
     * @see #valuesIterator()
     */
    public int getUniqueCount(){
        return freqTable.keySet().size();
    }

    /**
     * Returns the percentage of values that are equal to v
     * (as a proportion between 0 and 1).
     * <p>
     * Returns <code>Double.NaN</code> if no values have been added.
     * Returns 0 if at least one value has been added, but v is not comparable
     * to the values set.</p>
     *
     * @param v the value to lookup
     * @return the proportion of values equal to v
     */
    public double getPct(Comparable<?> v) {
        final long sumFreq = getSumFreq();
        if (sumFreq == 0) {
            return Double.NaN;
        }
        return (double) getCount(v) / (double) sumFreq;
    }

    /**
     * Returns the percentage of values that are equal to v
     * (as a proportion between 0 and 1).
     *
     * @param v the value to lookup
     * @return the proportion of values equal to v
     */
    public double getPct(int v) {
        return getPct(Long.valueOf(v));
    }

    /**
     * Returns the percentage of values that are equal to v
     * (as a proportion between 0 and 1).
     *
     * @param v the value to lookup
     * @return the proportion of values equal to v
     */
    public double getPct(long v) {
        return getPct(Long.valueOf(v));
    }

    /**
     * Returns the percentage of values that are equal to v
     * (as a proportion between 0 and 1).
     *
     * @param v the value to lookup
     * @return the proportion of values equal to v
     */
    public double getPct(char v) {
        return getPct(Character.valueOf(v));
    }

    //-----------------------------------------------------------------------------------------

    /**
     * Returns the cumulative frequency of values less than or equal to v.
     * <p>
     * Returns 0 if v is not comparable to the values set.</p>
     *
     * @param v the value to lookup.
     * @return the proportion of values equal to v
     */
    @SuppressWarnings({ "rawtypes", "unchecked" })
    public long getCumFreq(Comparable<?> v) {
        if (getSumFreq() == 0) {
            return 0;
        }
        if (v instanceof Integer) {
            return getCumFreq(((Integer) v).longValue());
        }
        Comparator<Comparable<?>> c = (Comparator<Comparable<?>>) freqTable.comparator();
        if (c == null) {
            c = new NaturalComparator();
        }
        long result = 0;

        try {
            Long value = freqTable.get(v);
            if (value != null) {
                result = value.longValue();
            }
        } catch (ClassCastException ex) {
            return result;   // v is not comparable
        }

        if (c.compare(v, freqTable.firstKey()) < 0) {
            return 0;  // v is comparable, but less than first value
        }

        if (c.compare(v, freqTable.lastKey()) >= 0) {
            return getSumFreq();    // v is comparable, but greater than the last value
        }

        Iterator<Comparable<?>> values = valuesIterator();
        while (values.hasNext()) {
            Comparable<?> nextValue = values.next();
            if (c.compare(v, nextValue) > 0) {
                result += getCount(nextValue);
            } else {
                return result;
            }
        }
        return result;
    }

     /**
     * Returns the cumulative frequency of values less than or equal to v.
     * <p>
     * Returns 0 if v is not comparable to the values set.</p>
     *
     * @param v the value to lookup
     * @return the proportion of values equal to v
     */
    public long getCumFreq(int v) {
        return getCumFreq(Long.valueOf(v));
    }

     /**
     * Returns the cumulative frequency of values less than or equal to v.
     * <p>
     * Returns 0 if v is not comparable to the values set.</p>
     *
     * @param v the value to lookup
     * @return the proportion of values equal to v
     */
    public long getCumFreq(long v) {
        return getCumFreq(Long.valueOf(v));
    }

    /**
     * Returns the cumulative frequency of values less than or equal to v.
     * <p>
     * Returns 0 if v is not comparable to the values set.</p>
     *
     * @param v the value to lookup
     * @return the proportion of values equal to v
     */
    public long getCumFreq(char v) {
        return getCumFreq(Character.valueOf(v));
    }

    //----------------------------------------------------------------------------------------------

    /**
     * Returns the cumulative percentage of values less than or equal to v
     * (as a proportion between 0 and 1).
     * <p>
     * Returns <code>Double.NaN</code> if no values have been added.
     * Returns 0 if at least one value has been added, but v is not comparable
     * to the values set.</p>
     *
     * @param v the value to lookup
     * @return the proportion of values less than or equal to v
     */
    public double getCumPct(Comparable<?> v) {
        final long sumFreq = getSumFreq();
        if (sumFreq == 0) {
            return Double.NaN;
        }
        return (double) getCumFreq(v) / (double) sumFreq;
    }

    /**
     * Returns the cumulative percentage of values less than or equal to v
     * (as a proportion between 0 and 1).
     * <p>
     * Returns 0 if v is not comparable to the values set.</p>
     *
     * @param v the value to lookup
     * @return the proportion of values less than or equal to v
     */
    public double getCumPct(int v) {
        return getCumPct(Long.valueOf(v));
    }

    /**
     * Returns the cumulative percentage of values less than or equal to v
     * (as a proportion between 0 and 1).
     * <p>
     * Returns 0 if v is not comparable to the values set.</p>
     *
     * @param v the value to lookup
     * @return the proportion of values less than or equal to v
     */
    public double getCumPct(long v) {
        return getCumPct(Long.valueOf(v));
    }

    /**
     * Returns the cumulative percentage of values less than or equal to v
     * (as a proportion between 0 and 1).
     * <p>
     * Returns 0 if v is not comparable to the values set.</p>
     *
     * @param v the value to lookup
     * @return the proportion of values less than or equal to v
     */
    public double getCumPct(char v) {
        return getCumPct(Character.valueOf(v));
    }

    /**
     * Returns the mode value(s) in comparator order.
     *
     * @return a list containing the value(s) which appear most often.
     * @since 3.3
     */
    public List<Comparable<?>> getMode() {
        long mostPopular = 0; // frequencies are always positive

        // Get the max count first, so we avoid having to recreate the List each time
        for(Long l : freqTable.values()) {
            long frequency = l.longValue();
            if (frequency > mostPopular) {
                mostPopular = frequency;
            }
        }

        List<Comparable<?>> modeList = new ArrayList<Comparable<?>>();
        for (Entry<Comparable<?>, Long> ent : freqTable.entrySet()) {
            long frequency = ent.getValue().longValue();
            if (frequency == mostPopular) {
               modeList.add(ent.getKey());
            }
        }
        return modeList;
    }

    //----------------------------------------------------------------------------------------------

    /**
     * Merge another Frequency object's counts into this instance.
     * This Frequency's counts will be incremented (or set when not already set)
     * by the counts represented by other.
     *
     * @param other the other {@link Frequency} object to be merged
     * @throws NullArgumentException if {@code other} is null
     * @since 3.1
     */
    public void merge(final Frequency other) throws NullArgumentException {
        MathUtils.checkNotNull(other, LocalizedFormats.NULL_NOT_ALLOWED);

        final Iterator<Map.Entry<Comparable<?>, Long>> iter = other.entrySetIterator();
        while (iter.hasNext()) {
            final Map.Entry<Comparable<?>, Long> entry = iter.next();
            incrementValue(entry.getKey(), entry.getValue().longValue());
        }
    }

    /**
     * Merge a {@link Collection} of {@link Frequency} objects into this instance.
     * This Frequency's counts will be incremented (or set when not already set)
     * by the counts represented by each of the others.
     *
     * @param others the other {@link Frequency} objects to be merged
     * @throws NullArgumentException if the collection is null
     * @since 3.1
     */
    public void merge(final Collection<Frequency> others) throws NullArgumentException {
        MathUtils.checkNotNull(others, LocalizedFormats.NULL_NOT_ALLOWED);

        for (final Frequency freq : others) {
            merge(freq);
        }
    }

    //----------------------------------------------------------------------------------------------

    /**
     * A Comparator that compares comparable objects using the
     * natural order.  Copied from Commons Collections ComparableComparator.
     * @param <T> the type of the objects compared
     */
    private static class NaturalComparator<T extends Comparable<T>> implements Comparator<Comparable<T>>, Serializable {

        /** Serializable version identifier */
        private static final long serialVersionUID = -3852193713161395148L;

        /**
         * Compare the two {@link Comparable Comparable} arguments.
         * This method is equivalent to:
         * <pre>(({@link Comparable Comparable})o1).{@link Comparable#compareTo compareTo}(o2)</pre>
         *
         * @param  o1 the first object
         * @param  o2 the second object
         * @return  result of comparison
         * @throws NullPointerException when <i>o1</i> is <code>null</code>,
         *         or when <code>((Comparable)o1).compareTo(o2)</code> does
         * @throws ClassCastException when <i>o1</i> is not a {@link Comparable Comparable},
         *         or when <code>((Comparable)o1).compareTo(o2)</code> does
         */
        @SuppressWarnings("unchecked") // cast to (T) may throw ClassCastException, see Javadoc
        public int compare(Comparable<T> o1, Comparable<T> o2) {
            return o1.compareTo((T) o2);
        }
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result +
                 ((freqTable == null) ? 0 : freqTable.hashCode());
        return result;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!(obj instanceof Frequency)) {
            return false;
        }
        Frequency other = (Frequency) obj;
        if (freqTable == null) {
            if (other.freqTable != null) {
                return false;
            }
        } else if (!freqTable.equals(other.freqTable)) {
            return false;
        }
        return true;
    }

}
