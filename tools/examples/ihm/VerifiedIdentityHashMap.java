/*
 * Copyright (c) 2000, 2017, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package ihm;

//import sun.misc.SharedSecrets;

/**
 * This class implements the <tt>Map</tt> interface with a hash table, using
 * reference-equality in place of object-equality when comparing keys (and
 * values).  In other words, in an <tt>VerifiedIdentityHashMap</tt>, two keys
 * <tt>k1</tt> and <tt>k2</tt> are considered equal if and only if
 * <tt>(k1==k2)</tt>.  (In normal <tt>Map</tt> implementations (like
 * <tt>HashMap</tt>) two keys <tt>k1</tt> and <tt>k2</tt> are considered equal
 * if and only if <tt>(k1==null ? k2==null : k1.equals(k2))</tt>.)
 *
 * <p><b>This class is <i>not</i> a general-purpose <tt>Map</tt>
 * implementation!  While this class implements the <tt>Map</tt> interface, it
 * intentionally violates <tt>Map's</tt> general contract, which mandates the
 * use of the <tt>equals</tt> method when comparing objects.  This class is
 * designed for use only in the rare cases wherein reference-equality
 * semantics are required.</b>
 *
 * <p>A typical use of this class is <i>topology-preserving object graph
 * transformations</i>, such as serialization or deep-copying.  To perform such
 * a transformation, a program must maintain a "node table" that keeps track
 * of all the object references that have already been processed.  The node
 * table must not equate distinct objects even if they happen to be equal.
 * Another typical use of this class is to maintain <i>proxy objects</i>.  For
 * example, a debugging facility might wish to maintain a proxy object for
 * each object in the program being debugged.
 *
 * <p>This class provides all of the optional map operations, and permits
 * <tt>null</tt> values and the <tt>null</tt> key.  This class makes no
 * guarantees as to the order of the map; in particular, it does not guarantee
 * that the order will remain constant over time.
 *
 * <p>This class provides constant-time performance for the basic
 * operations (<tt>get</tt> and <tt>put</tt>), assuming the system
 * identity hash function ({@link System#identityHashCode(Object)})
 * disperses elements properly among the buckets.
 *
 * <p>This class has one tuning parameter (which affects performance but not
 * semantics): <i>expected maximum size</i>.  This parameter is the maximum
 * number of key-value mappings that the map is expected to hold.  Internally,
 * this parameter is used to determine the number of buckets initially
 * comprising the hash table.  The precise relationship between the expected
 * maximum size and the number of buckets is unspecified.
 *
 * <p>If the size of the map (the number of key-value mappings) sufficiently
 * exceeds the expected maximum size, the number of buckets is increased.
 * Increasing the number of buckets ("rehashing") may be fairly expensive, so
 * it pays to create identity hash maps with a sufficiently large expected
 * maximum size.  On the other hand, iteration over collection views requires
 * time proportional to the number of buckets in the hash table, so it
 * pays not to set the expected maximum size too high if you are especially
 * concerned with iteration performance or memory usage.
 *
 * <p><strong>Note that this implementation is not synchronized.</strong>
 * If multiple threads access an identity hash map concurrently, and at
 * least one of the threads modifies the map structurally, it <i>must</i>
 * be synchronized externally.  (A structural modification is any operation
 * that adds or deletes one or more mappings; merely changing the value
 * associated with a key that an instance already contains is not a
 * structural modification.)  This is typically accomplished by
 * synchronizing on some object that naturally encapsulates the map.
 * <p>
 * If no such object exists, the map should be "wrapped" using the
 * {@link Collections#synchronizedMap Collections.synchronizedMap}
 * method.  This is best done at creation time, to prevent accidental
 * unsynchronized access to the map:<pre>
 *   Map m = Collections.synchronizedMap(new VerifiedIdentityHashMap(...));</pre>
 *
 * <p>The iterators returned by the <tt>iterator</tt> method of the
 * collections returned by all of this class's "collection view
 * methods" are <i>fail-fast</i>: if the map is structurally modified
 * at any time after the iterator is created, in any way except
 * through the iterator's own <tt>remove</tt> method, the iterator
 * will throw a {@link ConcurrentModificationException}.  Thus, in the
 * face of concurrent modification, the iterator fails quickly and
 * cleanly, rather than risking arbitrary, non-deterministic behavior
 * at an undetermined time in the future.
 *
 * <p>Note that the fail-fast behavior of an iterator cannot be guaranteed
 * as it is, generally speaking, impossible to make any hard guarantees in the
 * presence of unsynchronized concurrent modification.  Fail-fast iterators
 * throw <tt>ConcurrentModificationException</tt> on a best-effort basis.
 * Therefore, it would be wrong to write a program that depended on this
 * exception for its correctness: <i>fail-fast iterators should be used only
 * to detect bugs.</i>
 *
 * <p>Implementation note: This is a simple <i>linear-probe</i> hash table,
 * as described for example in texts by Sedgewick and Knuth.  The array
 * alternates holding keys and values.  (This has better locality for large
 * tables than does using separate arrays.)  For many JRE implementations
 * and operation mixes, this class will yield better performance than
 * {@link HashMap} (which uses <i>chaining</i> rather than linear-probing).
 *
 * <p>This class is a member of the
 * <a href="{@docRoot}/../technotes/guides/collections/index.html">
 * Java Collections Framework</a>.
 *
 * @author Doug Lea and Josh Bloch
 * @see System#identityHashCode(Object)
 * @see Object#hashCode()
 * @see Collection
 * @see Map
 * @see HashMap
 * @see TreeMap
 * @since 1.4
 */

public class VerifiedIdentityHashMap
        extends AbstractMap
        implements Map, java.io.Serializable, Cloneable {

    /*+KEY@ // JML specifically for KeY
      @ public invariant
      @   table != null &&
      @   MINIMUM_CAPACITY * (\bigint)2 <= table.length  &&
      @   MAXIMUM_CAPACITY * (\bigint)2 >= table.length;
      @
      @ // For all key-value pairs: if key == null, then value == null
      @ public invariant
      @   (\forall \bigint i;
      @         0 <= i && i < table.length / (\bigint)2;
      @         (table[i * 2] == null ==> table[i * 2 + 1] == null));
      @
      @ // Non-empty keys are unique
      @ public invariant
      @   (\forall \bigint i; 0 <= i && i < table.length / (\bigint)2;
      @       (\forall \bigint j;
      @       i <= j && j < table.length / (\bigint)2;
      @       (table[2 * i] != null && table[2 * i] == table[2 * j]) ==> i == j));
      @
      @ // Size equals the number of non-empty keys in the table
      @ public invariant
      @   size == (\num_of \bigint i;
      @       0 <= i < table.length / (\bigint)2;
      @       table[2 * i] != null);
      @
      @ // Table length is a power of two
      @ public invariant
      @   (\exists \bigint i;
      @       0 <= i < table.length;
      @       \dl_pow(2,i) == table.length);
      @
      @ // Table length is always an even number
      @ public invariant 
      @   table.length % (\bigint)2 == 0;
      @
      @ // Table must have at least one empty key-element to prevent
      @ // infinite loops when a key is not present.
      @ public invariant
      @   (\exists \bigint i;
      @       0 <= i < table.length / (\bigint)2;
      @       table[2 * i] == null);
      @
      @ // There are no gaps between a key's hashed index and its actual
      @ // index (if the key is at a higher index than the hash code)
      @ public invariant
      @   (\forall \bigint i;
      @       0 <= i < table.length / (\bigint)2;
      @       table[2 * i] != null && 2 * i > \dl_genHash(table[2 * i], table.length) ==>
      @       (\forall \bigint j;
      @           \dl_genHash(table[2 * i], table.length) / (\bigint)2 <= j < i;
      @           table[2 * j] != null));
      @
      @ // There are no gaps between a key's hashed index and its actual
      @ // index (if the key is at a lower index than the hash code)
      @ public invariant
      @   (\forall \bigint i;
      @       0 <= i < table.length / (\bigint)2;
      @       table[2 * i] != null && 2 * i < \dl_genHash(table[2 * i], table.length) ==>
      @       (\forall \bigint j;
      @           \dl_genHash(table[2 * i], table.length) <= 2 * j < table.length || 0 <= 2 * j < 2 * i;
      @           table[2 * j] != null));
      @
      @ // All keys and values are of type Object
      @ public invariant
      @   \typeof(table) == \type(Object[]);
      @
      @ // Field modCount is of type integer (limits: 
      @ // Integer.MIN_VALUE and Integer.MAX_VALUE)
      @ public invariant
      @   \dl_inInt(modCount);
      @
      @*/
    /*+OPENJML@ // JML for non-KeY tools, i.e. JJBMC
      @ public invariant
      @   table != null; // &&
      @   //MINIMUM_CAPACITY * 2 <= table.length  && // is no longer valid as we set min and max to 4
      @   //MAXIMUM_CAPACITY * 2 >= table.length;
      @
      @ // For all key-value pairs: if key == null, then value == null
      @ public invariant
      @   (\forall int i;
      @         0 <= i && i < table.length / 2;
      @         (table[i * 2] == null ==> table[i * 2 + 1] == null));
      @
      @ // Non-empty keys are unique
      @ public invariant
      @   (\forall int i; 0 <= i && i < table.length / 2;
      @       (\forall int j;
      @       i <= j && j < table.length / 2;
      @       (table[2*i] != null && table[2*i] == table[2*j]) ==> i == j));
      @
//      @ // Size equals the number of non-empty keys in the table
//      @ public invariant
//      @   size == (\num_of int i;
//      @       0 <= i < table.length / 2;
//      @       table[2 * i] != null);
//      @
      @ // Table length is a power of two
      @ public invariant
      @   (table.length & (table.length - 1)) == 0;
      @
      @ // Table length is always an even number
      @ public invariant 
      @   table.length % 2 == 0;
      @
      @ // Table must have at least one empty key-element to prevent
      @ // infinite loops when a key is not present.
      @ public invariant
      @   (\exists int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] == null);
      @
      @ // There are no gaps between a key's hashed index and its actual
      @ // index (if the key is at a higher index than the hash code)
      @ public invariant
      @   (\forall int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] != null && 2*i > hash(table[2*i], table.length) ==>
      @       (\forall int j;
      @           hash(table[2*i], table.length) / 2 <= j < i;
      @           table[2*j] != null));
      @
//      @ // There are no gaps between a key's hashed index and its actual
//      @ // index (if the key is at a lower index than the hash code)
//      @ public invariant
//      @   (\forall int i;
//      @       0 <= i < table.length / 2;
//      @       table[2*i] != null && 2*i < hash(table[2*i], table.length) ==>
//      @       (\forall int j;
//      @           hash(table[2*i], table.length) <= 2*j < table.length || 0 <= 2*j < hash(table[2*i], table.length);
//      @           table[2*j] != null));
//      @
//      @ // All keys and values are of type Object
//      @ public invariant
//      @   \typeof(table) == \type(Object[]);
//      @
//      @ // Field modCount is of type integer (limits: 
//      @ // Integer.MIN_VALUE and Integer.MAX_VALUE)
//      @ public invariant
//      @   \dl_inInt(modCount);
      @*/

    /**
     * The initial capacity used by the no-args constructor.
     * MUST be a power of two.  The value 32 corresponds to the
     * (specified) expected maximum size of 21, given a load factor
     * of 2/3.
     */
    private /*@ spec_public @*/ static final int DEFAULT_CAPACITY = 32; // Original code. Disable for JJBMC
    // private /*@ spec_public @*/ static final int DEFAULT_CAPACITY =  4; // Enable for JJBMC

    /**
     * The minimum capacity, used if a lower value is implicitly specified
     * by either of the constructors with arguments.  The value 4 corresponds
     * to an expected maximum size of 2, given a load factor of 2/3.
     * MUST be a power of two.
     */
    private /*@ spec_public @*/ static final int MINIMUM_CAPACITY = 4;

    /**
     * The maximum capacity, used if a higher value is implicitly specified
     * by either of the constructors with arguments.
     * MUST be a power of two <= 1<<29.
     * <p>
     * In fact, the map can hold no more than MAXIMUM_CAPACITY-1 items
     * because it has to have at least one slot with the key == null
     * in order to avoid infinite loops in get(), put(), remove()
     */
    private /*@ spec_public @*/ static final int MAXIMUM_CAPACITY = 1 << 29; // Original code. Disable for JJBMC
    // private /*@ spec_public @*/ static final int MAXIMUM_CAPACITY =  4; // Enable for JJBMC

    /**
     * The table, resized as necessary. Length MUST always be a power of two.
     */
    private /*@ spec_public nullable @*/ transient Object[] table;

    /**
     * The number of key-value mappings contained in this identity hash map.
     *
     * @serial
     */
    private /*@ spec_public @*/ int size;

    /**
     * The number of modifications, to support fast-fail iterators
     */
    private /*@ spec_public @*/ transient int modCount;

    /**
     * Value representing null keys inside tables.
     */
    private /*@ spec_public @*/ static final Object NULL_KEY = new Object();

    /**
     * Use NULL_KEY for key if it is null.
     */
    /*@ private normal_behavior
      @   ensures key == null ==> \result == NULL_KEY;
      @   ensures key != null ==> \result == key;
      @*/
    private /*@ spec_public @*/ static /*@ strictly_pure @*/ Object maskNull(/*@ nullable @*/ Object key) {
        return (key == null ? NULL_KEY : key);
    }

    /**
     * Returns internal representation of null key back to caller as null.
     */
    /*@ private normal_behavior
      @   ensures key == NULL_KEY ==> \result == null;
      @   ensures key != NULL_KEY ==> \result == key;
      @*/
    private /*@ spec_public @*/ static /*@ strictly_pure nullable @*/ Object unmaskNull(Object key) {
        return (key == NULL_KEY ? null : key);
    }

    /**
     * Constructs a new, empty identity hash map with a default expected
     * maximum size (21).
     */
    /*+KEY@ 
      @ private normal_behavior
      @   ensures
      @     table != null &&
      @     table.length == (\bigint)2 * DEFAULT_CAPACITY &&
      @     keySet == null &&
      @     values == null &&
      @     entrySet == null &&
      @     modCount == 0 &&
      @     size == 0 &&
      @     (\forall \bigint i; 0 <= i && i < table.length; table[i] == null); 
      @*/
    /*+OPENJML@ 
      @ private normal_behavior
      @   ensures
      @     table != null &&
      @     table.length == 2 * DEFAULT_CAPACITY &&
      @     keySet == null &&
      @     values == null &&
      @     entrySet == null &&
      @     modCount == 0 &&
      @     size == 0 &&
      @     (\forall int i; 0 <= i && i < table.length; table[i] == null); 
      @*/
    public VerifiedIdentityHashMap() {
        init(DEFAULT_CAPACITY);
    }

    /**
     * Constructs a new, empty map with the specified expected maximum size.
     * Putting more than the expected number of key-value mappings into
     * the map may cause the internal data structure to grow, which may be
     * somewhat time-consuming.
     *
     * @param expectedMaxSize the expected maximum size of the map
     * @throws IllegalArgumentException if <tt>expectedMaxSize</tt> is negative
     */
    public VerifiedIdentityHashMap(int expectedMaxSize) {
        if (expectedMaxSize < 0)
            throw new IllegalArgumentException("expectedMaxSize is negative: "
                    + expectedMaxSize);
        init(capacity(expectedMaxSize));
    }

    /**
     * Returns the appropriate capacity for the given expected maximum size.
     * Returns the smallest power of two between MINIMUM_CAPACITY and
     * MAXIMUM_CAPACITY, inclusive, that is greater than (3 *
     * expectedMaxSize)/2, if such a number exists.  Otherwise returns
     * MAXIMUM_CAPACITY.
     */
    /*+KEY@ 
      @ private normal_behavior
      @   requires 
      @     expectedMaxSize > MAXIMUM_CAPACITY / (\bigint)3;
      @   ensures
      @     \result == MAXIMUM_CAPACITY;
      @     
      @ private normal_behavior
      @   requires 
      @     expectedMaxSize <= MAXIMUM_CAPACITY / (\bigint)3 &&
      @     expectedMaxSize <= (\bigint)2 * MINIMUM_CAPACITY / 3;
      @   ensures
      @     \result == MINIMUM_CAPACITY;
      @ 
      @ private normal_behavior
      @   requires 
      @     expectedMaxSize <= MAXIMUM_CAPACITY / (\bigint)3 &&
      @     expectedMaxSize > (\bigint)2 * MINIMUM_CAPACITY / 3;
      @   ensures
      @     \result <= ((\bigint)3 * expectedMaxSize) && 
      @     (\bigint)2 * \result > ((\bigint)3 * expectedMaxSize);
      @   ensures
      @     (\exists \bigint i;
      @       0 <= i < \result;
      @       \dl_pow(2,i) == \result); // result is a power of two
      @*/
    /*+OPENJML@ 
      @ private normal_behavior
      @   requires 
      @     expectedMaxSize > MAXIMUM_CAPACITY / 3;
      @   ensures
      @     \result == MAXIMUM_CAPACITY;
      @     
      @ private normal_behavior
      @   requires 
      @     expectedMaxSize <= MAXIMUM_CAPACITY / 3 &&
      @     expectedMaxSize <= 2 * MINIMUM_CAPACITY / 3;
      @   ensures
      @     \result == MINIMUM_CAPACITY;
      @ 
      @ private normal_behavior
      @   requires 
      @     expectedMaxSize <= MAXIMUM_CAPACITY / 3 &&
      @     expectedMaxSize > 2 * MINIMUM_CAPACITY / 3;
      @   ensures
      @     \result <= (3 * expectedMaxSize) && 
      @     2 * \result > (3 * expectedMaxSize);
      @   ensures
      @     (\result & (\result - 1)) == 0; // result is a power of two
      @*/
    private static /*@ strictly_pure @*/ int capacity(int expectedMaxSize) {
        // assert expectedMaxSize >= 0;
        return
                (expectedMaxSize > MAXIMUM_CAPACITY / 3) ? MAXIMUM_CAPACITY :
                        (expectedMaxSize <= 2 * MINIMUM_CAPACITY / 3) ? MINIMUM_CAPACITY :
                                Integer.highestOneBit(expectedMaxSize + (expectedMaxSize << 1));
    }

    /**
     * Initializes object to be an empty map with the specified initial
     * capacity, which is assumed to be a power of two between
     * MINIMUM_CAPACITY and MAXIMUM_CAPACITY inclusive.
     */
    /*+KEY@ 
      @ private normal_behavior
      @   requires
      @     (\exists \bigint i; 0 <= i < initCapacity; \dl_pow(2,i) == initCapacity) &&
      @     initCapacity >= MINIMUM_CAPACITY &&
      @     initCapacity <= MAXIMUM_CAPACITY &&
      @     \dl_inInt(modCount);
      @   assignable
      @     table;
      @   ensures
      @     table != null &&
      @     \typeof(table) == \type(Object[]) &&
      @     (\forall \bigint i; 0 <= i < table.length; table[i] == null) &&
      @     table.length == (\bigint)2 * initCapacity;
      @*/
    /*+OPENJML@ 
      @ private normal_behavior
      @   requires
      @     (initCapacity & (initCapacity - 1)) == 0 &&
      @     initCapacity >= MINIMUM_CAPACITY &&
      @     initCapacity <= MAXIMUM_CAPACITY;
      @   assignable
      @     table;
      @   ensures
      @     table != null &&
      @     (\forall int i; 0 <= i < table.length; table[i] == null) &&
      @     table.length == 2 * initCapacity;
      @*/
    private /*@ helper @*/ void init(int initCapacity) {
        // assert (initCapacity & -initCapacity) == initCapacity; // power of 2
        // assert initCapacity >= MINIMUM_CAPACITY;
        // assert initCapacity <= MAXIMUM_CAPACITY;

        table = new Object[2 * initCapacity];
    }

    /**
     * Constructs a new identity hash map containing the keys-value mappings
     * in the specified map.
     *
     * @param m the map whose mappings are to be placed into this map
     * @throws NullPointerException if the specified map is null
     */
    public VerifiedIdentityHashMap(Map m) {
        // Allow for a bit of growth
        this((int) ((1 + m.size()) * 1.1));
        putAll(m);
    }

    /**
     * Returns the number of key-value mappings in this identity hash map.
     *
     * @return the number of key-value mappings in this map
     */
    /*@ also
      @ public normal_behavior
      @   ensures
      @     \result == size;
      @*/
    public /*@ strictly_pure @*/ int size() {
        return size;
    }

    /**
     * Returns <tt>true</tt> if this identity hash map contains no key-value
     * mappings.
     *
     * @return <tt>true</tt> if this identity hash map contains no key-value
     * mappings
     */
    /*@ also
      @ public normal_behavior
      @   ensures
      @     \result <==> size == 0;
      @*/
    public /*@ strictly_pure @*/ boolean isEmpty() {
        return size == 0;
    }

    /**
     * Returns index for Object x.
     */
    /*+KEY@ 
      @ private normal_behavior
      @   ensures
      @     (x == null ==> \result == 0) &&
      @     \result == \dl_genHash(x, length) && 
      @     \result % 2 == 0 &&
      @     \result < length && 
      @     \result >= 0;
      @*/
    private /*@ spec_public @*/ static /*@ strictly_pure @*/ int hash(Object x, int length) {
        int h = System.identityHashCode(x);
        // Multiply by -127, and left-shift to use least bit as part of hash
        return ((h << 1) - (h << 8)) & (length - 1);
    }

    /**
     * Circularly traverses table of size len.
     */
    /*@ private normal_behavior
      @   ensures
      @     (i + 2 < len ==> \result == i + 2) &&
      @     (i + 2 >= len ==> \result == 0);
      @*/
    private static /*@ strictly_pure @*/ int nextKeyIndex(int i, int len) {
        return (i + 2 < len ? i + 2 : 0);
    }

    /**
     * Returns the value to which the specified key is mapped,
     * or {@code null} if this map contains no mapping for the key.
     *
     * <p>More formally, if this map contains a mapping from a key
     * {@code k} to a value {@code v} such that {@code (key == k)},
     * then this method returns {@code v}; otherwise it returns
     * {@code null}.  (There can be at most one such mapping.)
     *
     * <p>A return value of {@code null} does not <i>necessarily</i>
     * indicate that the map contains no mapping for the key; it's also
     * possible that the map explicitly maps the key to {@code null}.
     * The {@link #containsKey containsKey} operation may be used to
     * distinguish these two cases.
     *
     * @see #put(Object, Object)
     */
    /*+KEY@ 
      @ // Key exists
      @ also
      @ public normal_behavior
      @   requires
      @     (\exists \bigint i;
      @       0 <= i < table.length / (\bigint)2;
      @       table[i * 2] == maskNull(key));
      @   ensures
      @     (\exists \bigint i;
      @        0 <= i < table.length / (\bigint)2;
      @        table[i * 2] == maskNull(key) && \result == table[i * 2 + 1]);
      @      
      @ // Key does not exist       
      @ also
      @ public normal_behavior
      @   requires
      @     !(\exists \bigint i;
      @       0 <= i < table.length / (\bigint)2;
      @       table[i * 2] == maskNull(key));
      @   ensures
      @     \result == null;
      @*/
    /*+OPENJML@ 
      @ // Key exists
      @ also
      @ public normal_behavior
      @   requires
      @     (\exists int i;
      @       0 <= i < table.length / 2;
      @       table[i * 2] == maskNull(key));
      @   ensures
      @     (\exists int i;
      @        0 <= i < table.length / 2;
      @        table[i * 2] == maskNull(key) && \result == table[i * 2 + 1]);
      @      
      @ // Key does not exist       
      @ also
      @ public normal_behavior
      @   requires
      @     !(\exists int i;
      @       0 <= i < table.length / 2;
      @       table[i * 2] == maskNull(key));
      @   ensures
      @     \result == null;
      @*/
    public /*@ pure nullable @*/ java.lang.Object get(/*@ nullable @*/ Object key) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);

        //+KEY@ ghost \bigint hash = i;

        /*+KEY@
          @ // Index i is always an even value within the array bounds
          @ maintaining
          @   i >= 0 && i < len && i % (\bigint)2 == 0;
          @
          @ // Suppose i > hash. This can only be the case when no key k and no null is present
          @ // at an even index of tab in the interval [hash..i-2]. 
          @ maintaining
          @   (i > hash) ==>
          @   (\forall \bigint n; hash <= (2 * n) < i; tab[2 * n] != k && tab[2 * n] != null);
          @ 
          @ // Suppose i < hash. This can only be the case when no key k and no null is present
          @ // at an even index of tab in the intervals [0..i-2] and [hash..len-2]. 
          @ maintaining
          @   (i < hash) ==>
          @   (\forall \bigint n; hash <= (2 * n) < len; tab[2 * n] != k && tab[2 * n] != null) &&
          @   (\forall \bigint m; 0 <= (2 * m) < i; tab[2 * m] != k && tab[2 * m] != null);
          @   
          @ decreasing hash > i ? hash - i : hash + len - i;
          @ 
          @ assignable \strictly_nothing;
          @*/
        while (true) {
            Object item = tab[i];
            if (item == k)
                return (java.lang.Object) tab[i + 1];
            if (item == null)
                return null;
            i = nextKeyIndex(i, len);
        }
    }

    /**
     * Tests whether the specified object reference is a key in this identity
     * hash map.
     *
     * @param key possible key
     * @return <code>true</code> if the specified object reference is a key
     * in this map
     * @see #containsValue(Object)
     */
     /*+KEY@ 
       @ also
       @ public normal_behavior
       @   ensures
       @     \result <==> (\exists \bigint j;
       @         0 <= j < (table.length / (\bigint)2);
       @         table[j * 2] == maskNull(key));
       @*/
     /*+OPENJML@ 
       @ also
       @ public normal_behavior
       @   ensures
       @     \result <==> (\exists int j;
       @         0 <= j < (table.length / 2);
       @         table[j * 2] == maskNull(key));
       @*/
    public /*@ strictly_pure @*/ boolean containsKey(/*@ nullable @*/ Object key) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);

        //+KEY@ ghost \bigint hash = i;
        
        /*+KEY@
          @ // Index i is always an even value within the array bounds
          @ maintaining 
          @   i >= 0 && i < len && i % (\bigint)2 == 0;
          @
          @ // Suppose i > hash. This can only be the case when no key k and no null is present
          @ // at an even index of tab in the interval [hash..i-2]. 
          @ maintaining
          @   (i > hash) ==>
          @   (\forall \bigint n; hash <= (2 * n) < i; tab[2 * n] != k && tab[2 * n] != null);
          @ 
          @ // Suppose i < hash. This can only be the case when no key k and no null is present
          @ // at an even index of tab in the intervals [0..i-2] and [hash..len-2]. 
          @ maintaining
          @   (i < hash) ==>
          @   (\forall \bigint n; hash <= (2 * n) < len; tab[2 * n] != k && tab[2 * n] != null) &&
          @   (\forall \bigint m; 0 <= (2 * m) < i; tab[2 * m] != k && tab[2 * m] != null);
          @   
          @ decreasing hash > i ? hash - i : hash + len - i;
          @ 
          @ assignable \strictly_nothing;
          @*/
        while (true) {
            Object item = tab[i];
            if (item == k)
                return true;
            if (item == null)
                return false;
            i = nextKeyIndex(i, len);
        }
    }

    /**
     * Tests whether the specified object reference is a value in this identity
     * hash map.
     *
     * @param value value whose presence in this map is to be tested
     * @return <tt>true</tt> if this map maps one or more keys to the
     * specified object reference
     * @see #containsKey(Object)
     */
    /*+KEY@ 
      @ also
      @ public normal_behavior
      @   ensures
      @     \result <==> (\exists \bigint j;
      @         0 <= j < table.length / (\bigint)2;
      @         table[j * (\bigint)2] != null && table[j * (\bigint)2 + 1] == value);
      @*/
    /*+OPEN_JML@ 
      @ also
      @ public normal_behavior
      @   ensures
      @     \result <==> (\exists int j;
      @         0 <= j < table.length / 2;
      @         table[j * 2] != null && table[j * 2 + 1] == value);
      @*/
    public /*@ strictly_pure @*/ boolean containsValue(/*@ nullable @*/ Object value) {
        Object[] tab = table;

        /*+KEY@
          @ // Index i is always an odd value within the array bounds
          @ maintaining 
          @   i >= 1 && i <= tab.length+1 && i % (\bigint)2 == 1;
          @
          @ // There cannot be an odd index n < i containing the value we are looking for (unless
          @ // the associated key is null, in which case the value is ignored). 
          @ maintaining
          @   (\forall \bigint n; 1 <= n < i && n % 2 == 1; tab[n - 1] != null ==> tab[n] != value);
          @ 
          @ decreasing tab.length + 1 - i;
          @ 
          @ assignable \strictly_nothing;
          @*/
        for (int i = 1; i < tab.length; i += 2)
            if (tab[i] == value && tab[i - 1] != null)
                return true;

        return false;
    }

    /**
     * Tests if the specified key-value mapping is in the map.
     *
     * @param key   possible key
     * @param value possible value
     * @return <code>true</code> if and only if the specified key-value
     * mapping is in the map
     */
    /*+KEY@ 
      @ private normal_behavior
      @   ensures
      @     \result <==> (\exists \bigint i;
      @       0 <= i < table.length / (\bigint)2;
      @       table[i * 2] == maskNull(key) && table[i * 2 + 1] == value);
      @*/
    /*+OPENJML@ 
      @ private normal_behavior
      @   ensures
      @     \result <==> (\exists int i;
      @       0 <= i < table.length / 2;
      @       table[i * 2] == maskNull(key) && table[i * 2 + 1] == value);
      @*/
    private /*@ spec_public @*/ /*@ strictly_pure @*/ boolean containsMapping(Object key, Object value) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);

        //+KEY@ ghost \bigint hash = i;
        
        /*+KEY@
          @ // Index i is always an even value within the array bounds
          @ maintaining 
          @   i >= 0 && i < len && i % (\bigint)2 == 0;
          @
          @ // Suppose i > hash. This can only be the case when no key k and no null is present
          @ // at an even index of tab in the interval [hash..i-2]. 
          @ maintaining
          @   (i > hash) ==>
          @   (\forall \bigint n; hash <= (2 * n) < i; tab[2 * n] != k && tab[2 * n] != null);
          @ 
          @ // Suppose i < hash. This can only be the case when no key k and no null is present
          @ // at an even index of tab in the intervals [0..i-2] and [hash..len-2]. 
          @ maintaining
          @   (i < hash) ==>
          @   (\forall \bigint n; hash <= (2 * n) < len; tab[2 * n] != k && tab[2 * n] != null) &&
          @   (\forall \bigint m; 0 <= (2 * m) < i; tab[2 * m] != k && tab[2 * m] != null);
          @   
          @ decreasing hash > i ? hash - i : hash + len - i;
          @ 
          @ assignable \strictly_nothing;
          @*/
        while (true) {
            Object item = tab[i];
            if (item == k)
                return tab[i + 1] == value;
            if (item == null)
                return false;
            i = nextKeyIndex(i, len);
        }
    }

    /**
     * Associates the specified value with the specified key in this identity
     * hash map.  If the map previously contained a mapping for the key, the
     * old value is replaced.
     *
     * @param key   the key with which the specified value is to be associated
     * @param value the value to be associated with the specified key
     * @return the previous value associated with <tt>key</tt>, or
     * <tt>null</tt> if there was no mapping for <tt>key</tt>.
     * (A <tt>null</tt> return can also indicate that the map
     * previously associated <tt>null</tt> with <tt>key</tt>.)
     * @see Object#equals(Object)
     * @see #get(Object)
     * @see #containsKey(Object)
     */
    /*+KEY@ 
      @ also
      @ private exceptional_behavior
      @   requires
      @     size == MAXIMUM_CAPACITY - 1;
      @   requires
      @     // The key is not present in the table
      @     !(\exists \bigint i;
      @         0 <= i < table.length / (\bigint)2;
      @         table[i * 2] == maskNull(key));
      @   assignable
      @     \nothing;
      @   signals_only
      @     IllegalStateException;
      @   signals
      @     (IllegalStateException e) true;
      @ also
      @ public normal_behavior
      @   requires
      @     // The key is already present in the table
      @     (\exists \bigint i;
      @         0 <= i < table.length / (\bigint)2;
      @         table[i*2] == maskNull(key));
      @   assignable
      @     table[*];
      @   ensures
      @     // The new value is associated with key and
      @     // the old value associated with key is returned
      @     (\exists \bigint i;
      @         0 <= i < table.length / (\bigint)2;
      @         table[i*2] == maskNull(key) &&
      @         \result == \old(table[i * 2 + 1]) &&
      @         table[i * 2 + 1] == value);
      @   ensures
      @     // After execution, all keys are unchanged and all old values are unchanged
      @     // except the old value that was associated with key
      @     (\forall \bigint i;
      @         0 <= i < \old(table.length) / (\bigint)2;
      @         (\old(table[i * 2]) == table[i * 2]) &&
      @         (\old(table[i * 2]) != maskNull(key) ==>
      @             \old(table[i * 2 + 1]) == table[i * 2 + 1]));
      @ also
      @ public normal_behavior
      @   requires
      @     size < MAXIMUM_CAPACITY - 1;
      @   requires
      @     // The key is not present in the table
      @     !(\exists \bigint i;
      @         0 <= i < table.length / (\bigint)2;
      @         table[i * 2] == maskNull(key));
      @   assignable
      @     size, table[*], modCount, table;
      @   ensures
      @     // size must be increased by 1, modCount must change, and null must be returned
      @     size == \old(size) + 1 && modCount != \old(modCount) && \result == null;
      @   ensures
      @     // After execution, all old keys are still present and all old values are still present
      @     (\forall \bigint i;
      @         0 <= i < \old(table.length) / (\bigint)2;
      @         (\exists \bigint j;
      @             0 <= j < table.length / (\bigint)2;
      @             (\old(table[i * 2]) == table[j * 2]) &&
      @              \old(table[i * 2 + 1]) == table[j * 2 + 1]));
      @   ensures
      @     // After execution, the table contains the new key associated with the new value
      @     (\exists \bigint i;
      @         0 <= i < table.length / (\bigint)2;
      @         table[i * 2] == maskNull(key) && table[i * 2 + 1] == value);
      @*/
    /*+OPENJML@ 
      @ also
      @ public normal_behavior
      @   requires
      @     // The key is already present in the table
      @     (\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i*2] == maskNull(key));
      @   assignable
      @     table[*];
      @   ensures
      @     // The new value is associated with key and
      @     // the old value associated with key is returned
      @     (\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i*2] == maskNull(key) &&
      @         \result == \old(table[i * 2 + 1]) &&
      @         table[i * 2 + 1] == value);
      @   ensures
      @     // After execution, all keys are unchanged and all old values are unchanged
      @     // except the old value that was associated with key
      @     (\forall int i;
      @         0 <= i < \old(table.length) / 2;
      @         (\old(table[i * 2]) == table[i * 2]) &&
      @         (\old(table[i * 2]) != maskNull(key) ==>
      @             \old(table[i * 2 + 1]) == table[i * 2 + 1]));
      @ also
      @ public normal_behavior
      @   requires
      @     size < MAXIMUM_CAPACITY - 1;
      @   requires
      @     // The key is not present in the table
      @     !(\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i * 2] == maskNull(key));
      @   assignable
      @     size, table[*], modCount, table;
      @   ensures
      @     // size must be increased by 1, modCount must change, and null must be returned
      @     size == \old(size) + 1 && modCount != \old(modCount) && \result == null;
      @   ensures
      @     // After execution, all old keys are still present and all old values are still present
      @     (\forall int i;
      @         0 <= i < \old(table.length) / 2;
      @         (\exists int j;
      @             0 <= j < table.length / 2;
      @             (\old(table[i * 2]) == table[j * 2]) &&
      @              \old(table[i * 2 + 1]) == table[j * 2 + 1]));
      @   ensures
      @     // After execution, the table contains the new key associated with the new value
      @     (\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i * 2] == maskNull(key) && table[i * 2 + 1] == value);
      @*/
    public /*@ nullable @*/ java.lang.Object put(/*@ nullable @*/ java.lang.Object key, /*@ nullable @*/ java.lang.Object value) {
        final Object k = maskNull(key);

        retryAfterResize:
        for (; ; ) {
            final Object[] tab = table;
            final int len = tab.length;
            int i = hash(k, len);

            //+KEY@ ghost \bigint hash = i;
        
          /*+KEY@
            @ // Index i is always an even value within the array bounds
            @ maintaining 
            @   tab == table && len == tab.length &&
            @   i >= 0 && i < (len - (\bigint)1) && i % (\bigint)2 == 0;
            @
            @ // Suppose i > hash. This can only be the case when no key k and no null is present
            @ // at an even index of tab in the interval [hash..i-2]. 
            @ maintaining
            @   (i > hash) ==>
            @   (\forall \bigint n; hash <= (2 * n) < i; tab[2 * n] != k && tab[2 * n] != null);
            @ 
            @ // Suppose i < hash. This can only be the case when no key k and no null is present
            @ // at an even index of tab in the intervals [0..i-2] and [hash..len-2]. 
            @ maintaining
            @   (i < hash) ==>
            @   (\forall \bigint n; hash <= (2 * n) < len; tab[2 * n] != k && tab[2 * n] != null) &&
            @   (\forall \bigint m; 0 <= (2 * m) < i; tab[2 * m] != k && tab[2 * m] != null);
            @
            @ decreasing hash > i ? hash - i : len + hash - i;
            @
            @ // if the loop iteration completes, the heap is unchanged 
            @ // in case key is present, table is updated but the loop iteration terminates without
            @ // completing because the method returns, so the assignable clause need not hold
            @ assignable \strictly_nothing;
            @*/
            for (Object item; (item = tab[i]) != null;
                 i = nextKeyIndex(i, len)) {
                if (item == k) {
                    java.lang.Object oldValue = (java.lang.Object) tab[i + 1];
                    tab[i + 1] = value;
                    return oldValue;
                }
            }

            final int s = size + 1;
            // Use optimized form of 3 * s.
            // Next capacity is len, 2 * current capacity.
            if (s + (s << 1) > len && resize(len))
                continue retryAfterResize;

            modCount++;
            tab[i] = k;
            tab[i + 1] = value;
            size = s;
            return null;
        }
    }

    /**
     * Resizes the table if necessary to hold given capacity.
     *
     * @param newCapacity the new capacity, must be a power of two.
     * @return whether a resize did in fact take place
     */
    /*+KEY@ 
      @ // Throws an exception when table.length == 2 * MAXIMUM_CAPACITY &&
      @ // size == MAXIMUM_CAPACITY - 1.
      @ private exceptional_behavior
      @   requires
      @     table.length == (\bigint)2 * MAXIMUM_CAPACITY &&
      @     size == MAXIMUM_CAPACITY - 1;
      @   assignable
      @     \nothing;
      @   signals_only
      @     IllegalStateException;
      @   signals
      @     (IllegalStateException e) true;
      @
      @ // Nothing changes if table.length == 2 * MAXIMUM_CAPACITY &&
      @ // size < MAXIMUM_CAPACITY - 1.
      @ private normal_behavior
      @   requires
      @     table.length == (\bigint)2 * MAXIMUM_CAPACITY &&
      @     size < MAXIMUM_CAPACITY - 1;
      @   assignable
      @     \strictly_nothing;
      @   ensures
      @     \result == false;
      @
      @ // Nothing changes when table.length < 2 * MAXIMUM_CAPACITY &&
      @ // table.length >= 2 * newCapacity.
      @ private normal_behavior
      @   requires
      @     table.length < (\bigint)2 * MAXIMUM_CAPACITY &&
      @     table.length >= (\bigint)2 * newCapacity &&
      @     newCapacity >= MINIMUM_CAPACITY &&
      @     newCapacity <= (\bigint)2 * MAXIMUM_CAPACITY;
      @
      @   assignable
      @     \strictly_nothing;
      @
      @   ensures
      @     // Map is unchanged, so return false
      @     \result == false;
      @
      @
      @ // If we actually resize (table.length < 2 * MAXIMUM_CAPACITY && table.length < 2 * newCapacity)
      @ // then rehash the table with the new length to re-establish the class invariant.
      @ private normal_behavior
      @   requires
      @     table.length < (\bigint)2 * newCapacity &&
      @     newCapacity <= MAXIMUM_CAPACITY &&
      @     newCapacity >= MINIMUM_CAPACITY &&
      @     (\exists \bigint i;
      @       0 <= i < newCapacity;
      @       \dl_pow(2,i) == newCapacity);
      @
      @   assignable
      @     table, table[*];
      @
      @   ensures
      @     table.length == (newCapacity * (\bigint)2);
      @
      @   ensures
      @     // After execution, all old entries are still present
      @     (\forall \bigint i;
      @       0 <= i < \old(table.length) && i % 2 == 0;
      @       (\exists \bigint j;
      @         0 <= j < table.length && j % 2 == 0;
      @         \old(table[i]) == table[j] && \old(table[i + 1]) == table[j + 1]));
      @
      @   ensures
      @     // Map is changed, so return true
      @     \result == true;
      @
      @   ensures
      @     \fresh(table);
      @
      @   ensures 
      @     // All entries in the new table were also present in \old(table)
      @     (\forall \bigint n;
      @       0 <= n < table.length / (\bigint)2;
      @       (\exists \bigint m;
      @         0 <= m < \old(table.length) / (\bigint)2;
      @         table[2*n] == \old(table[2*m]) && table[2*n + 1] == \old(table[2*m + 1])));
      @*/
    /*+OPENJML@ 
      @ // Nothing changes if table.length == 2 * MAXIMUM_CAPACITY &&
      @ // size < MAXIMUM_CAPACITY - 1.
      @ private normal_behavior
      @   requires
      @     table.length == 2 * MAXIMUM_CAPACITY &&
      @     size < MAXIMUM_CAPACITY - 1;
      @   assignable
      @     \strictly_nothing;
      @   ensures
      @     \result == false;
      @
      @ // Nothing changes when table.length < 2 * MAXIMUM_CAPACITY &&
      @ // table.length >= 2 * newCapacity.
      @ private normal_behavior
      @   requires
      @     table.length < 2 * MAXIMUM_CAPACITY &&
      @     table.length >= 2 * newCapacity &&
      @     newCapacity >= MINIMUM_CAPACITY &&
      @     newCapacity <= 2 * MAXIMUM_CAPACITY;
      @
      @   assignable
      @     \strictly_nothing;
      @
      @   ensures
      @     // Map is unchanged, so return false
      @     \result == false;
      @
      @
      @ // If we actually resize (table.length < 2 * MAXIMUM_CAPACITY && table.length < 2 * newCapacity)
      @ // then rehash the table with the new length to re-establish the class invariant.
      @ private normal_behavior
      @   requires
      @     table.length < 2 * newCapacity &&
      @     newCapacity <= MAXIMUM_CAPACITY &&
      @     newCapacity >= MINIMUM_CAPACITY &&
      @     (\exists int i;
      @       0 <= i < newCapacity;
      @       (newCapacity & (newCapacity - 1)) == 0);
      @
      @   assignable
      @     table, table[*];
      @
      @   ensures
      @     table.length == (newCapacity * 2);
      @
      @   ensures
      @     // After execution, all old entries are still present
      @     (\forall int i;
      @       0 <= i < \old(table.length) && i % 2 == 0;
      @       (\exists int j;
      @         0 <= j < table.length && j % 2 == 0;
      @         \old(table[i]) == table[j] && \old(table[i + 1]) == table[j + 1]));
      @
      @   ensures
      @     // Map is changed, so return true
      @     \result == true;
      @
      @   ensures
      @     \fresh(table);
      @
      @   ensures 
      @     // All entries in the new table were also present in \old(table)
      @     (\forall int n;
      @       0 <= n < table.length / 2;
      @       (\exists int m;
      @         0 <= m < \old(table.length) / 2;
      @         table[2*n] == \old(table[2*m]) && table[2*n + 1] == \old(table[2*m + 1])));
      @*/
    private boolean resize(int newCapacity)
    // assert (newCapacity & -newCapacity) == newCapacity; // power of 2
    {
        int newLength = newCapacity * 2;

        Object[] oldTable = table;
        int oldLength = oldTable.length;
        if (oldLength == 2 * MAXIMUM_CAPACITY) { // can't expand any further
            if (size == MAXIMUM_CAPACITY - 1)
                throw new IllegalStateException("Capacity exhausted.");
            return false;
        }
        if (oldLength >= newLength)
            return false;

        Object[] newTable = new Object[newLength];

        /*+KEY@
          @ // All processed entries are copied to newTable
          @ maintaining 
          @   (\forall \bigint k;
          @     0 <= k < j && k % 2 == 0;
          @     (\exists \bigint l;
          @         0 <= l < newTable.length && l % 2 == 0;
          @         \old(table[k]) == newTable[l] && \old(table[k + 1]) == newTable[l + 1]));
          @
          @ // All (non-null) entries in newTable are also present in \old(table)
          @ maintaining 
          @   (\forall \bigint n;
          @     0 <= n < newTable.length && n % 2 == 0 && newTable[n] != null;
          @     (\exists \bigint m;
          @         0 <= m < j && m % 2 == 0;
          @         newTable[n] == \old(table[m]) && newTable[n + 1] == \old(table[m + 1])));
          @
          @ // All unprocessed entries are still untouched in old table
          @ maintaining 
          @   (\forall \bigint k;
          @     j <= k < \old(table.length);
          @     \old(table[k]) == oldTable[k]);
          @
          @ // The number of non-null keys in newTable equals the number of copied keys
          @ maintaining
          @    (\num_of \bigint i; 0 <= i < j / (\bigint)2; \old(table[2 * i]) != null)
          @ == (\num_of \bigint i; 0 <= i < newTable.length / (\bigint)2; newTable[2 * i] != null);
          @
          @ // For all key-value pairs: if key == null, then value == null
          @ maintaining
          @   (\forall \bigint i;
          @         0 <= i && i < newTable.length / (\bigint)2;
          @         (newTable[i * (\bigint)2] == null ==> newTable[i * (\bigint)2 + 1] == null));
          @
          @ // Non-empty keys in newTable are unique
          @ maintaining
          @   (\forall \bigint p; 0 <= p && p < newTable.length / (\bigint)2;
          @       (\forall \bigint q;
          @       p <= q && q < newTable.length / (\bigint)2;
          @       (newTable[2 * p] != null && newTable[2 * p] == newTable[2 * q]) ==> p == q));
          @
          @ // There are no gaps between a key's hashed index and its actual
          @ // index (if the key is at a higher index than the hash code)
          @ maintaining
          @   (\forall \bigint g;
          @       0 <= g < newTable.length / (\bigint)2;
          @       newTable[2 * g] != null && 2 * g > \dl_genHash(newTable[2 * g], newTable.length) ==>
          @       (\forall \bigint h;
          @           \dl_genHash(newTable[2 * g], newTable.length) / (\bigint)2 <= h < g;
          @           newTable[2 * h] != null));
          @
          @ // There are no gaps between a key's hashed index and its actual
          @ // index (if the key is at a lower index than the hash code)
          @ maintaining
          @   (\forall \bigint g;
          @       0 <= g < newTable.length / (\bigint)2;
          @       newTable[2 * g] != null && 2 * g < \dl_genHash(newTable[2 * g], newTable.length) ==>
          @       (\forall \bigint h;
          @           \dl_genHash(newTable[2 * g], newTable.length) <= 2 * h < newTable.length || 0 <= 2 * h < 2 * g;
          @           newTable[2 * h] != null));
          @
          @ // Table must have at least one empty key-element to prevent
          @ // infinite loops when a key is not present.
          @ maintaining
          @   (\exists \bigint i;
          @       0 <= i < newTable.length / (\bigint)2;
          @       newTable[2*i] == null);
          @
          @ maintaining
          @   j >= 0 && j <= oldLength && j % (\bigint)2 == 0;
          @ 
          @ assignable
          @   table[*], newTable[*];
          @
          @ decreasing
          @   oldLength - j;
          @*/
        for (int j = 0; j < oldLength; j += 2) {
            Object key = oldTable[j];
            if (key != null) {
                Object value = oldTable[j + 1];
                oldTable[j] = null;
                oldTable[j + 1] = null;
                int i = hash(key, newLength);

                //+KEY@ ghost \bigint hash = i;
                
                /*+KEY@
                  @ // Index i is always an even value within the array bounds
                  @ maintaining 
                  @   i >= 0 && i < newLength && i % (\bigint)2 == 0;
                  @
                  @ // There are no gaps in the segment [hash .. i)
                  @ // (if the current index is higher than the hash)
                  @ maintaining
                  @   (\forall \bigint g;
                  @       hash <= 2 * g < i;
                  @       newTable[2 * g] != null);
                  @
                  @ // There are no gaps in the segment [0 .. i) and [hash .. newLength)
                  @ // (if the current index is lower (wrap around) than the hash)
                  @ maintaining
                  @   (i < hash) ==>
                  @      (\forall \bigint g;
                  @          (0 <= 2 * g < i) || (hash <= 2 * g < newLength);
                  @          newTable[2 * g] != null);
                  @
                  @ assignable
                  @   \strictly_nothing;
                  @
                  @ decreasing
                  @   hash > i ? hash - i : newLength + hash - i;
                  @*/
                while (newTable[i] != null)
                    i = nextKeyIndex(i, newLength);
                newTable[i] = key;
                newTable[i + 1] = value;
            }
        }
        table = newTable;
        return true;
    }

    /**
     * Copies all of the mappings from the specified map to this map.
     * These mappings will replace any mappings that this map had for
     * any of the keys currently in the specified map.
     *
     * @param m mappings to be stored in this map
     * @throws NullPointerException if the specified map is null
     */
    public void putAll(Map m) {
        int n = m.size();
        if (n == 0)
            return;
        if (n > size)
            resize(capacity(n)); // conservatively pre-expand

        for (Object o : m.entrySet()) {
            Entry e = (Entry) o;
            put(e.getKey(), e.getValue());
        }
    }

    /**
     * Removes the mapping for this key from this map if present.
     *
     * @param key key whose mapping is to be removed from the map
     * @return the previous value associated with <tt>key</tt>, or
     * <tt>null</tt> if there was no mapping for <tt>key</tt>.
     * (A <tt>null</tt> return can also indicate that the map
     * previously associated <tt>null</tt> with <tt>key</tt>.)
     */
    public java.lang.Object remove(Object key) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);

        //+KEY@ ghost \bigint hash = i;
        
        /*+KEY@ 
          @ loop_invariant true; // TODO: see containsKey()
          @ decreasing len - (len + i - hash) % len;
          @ assignable i, modCount, size, tab[*];
          @*/
        while (true) {
            Object item = tab[i];
            if (item == k) {
                modCount++;
                size--;
                @SuppressWarnings("unchecked") java.lang.Object oldValue = (java.lang.Object) tab[i + 1];
                tab[i + 1] = null;
                tab[i] = null;
                closeDeletion(i);
                return oldValue;
            }
            if (item == null)
                return null;
            i = nextKeyIndex(i, len);
        }
    }

    /**
     * Removes the specified key-value mapping from the map if it is present.
     *
     * @param key   possible key
     * @param value possible value
     * @return <code>true</code> if and only if the specified key-value
     * mapping was in the map
     */
    private boolean removeMapping(Object key, Object value) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);

        while (true) {
            Object item = tab[i];
            if (item == k) {
                if (tab[i + 1] != value)
                    return false;
                modCount++;
                size--;
                tab[i] = null;
                tab[i + 1] = null;
                closeDeletion(i);
                return true;
            }
            if (item == null)
                return false;
            i = nextKeyIndex(i, len);
        }
    }

    /**
     * Rehash all possibly-colliding entries following a
     * deletion. This preserves the linear-probe
     * collision properties required by get, put, etc.
     *
     * @param d the index of a newly empty deleted slot
     */
    private void closeDeletion(int d)
    // Adapted from Knuth Section 6.4 Algorithm R
    {
        Object[] tab = table;
        int len = tab.length;

        // Look for items to swap into newly vacated slot
        // starting at index immediately following deletion,
        // and continuing until a null slot is seen, indicating
        // the end of a run of possibly-colliding keys.
        Object item;
        for (int i = nextKeyIndex(d, len); (item = tab[i]) != null;
             i = nextKeyIndex(i, len))
        // The following test triggers if the item at slot i (which
        // hashes to be at slot r) should take the spot vacated by d.
        // If so, we swap it in, and then continue with d now at the
        // newly vacated i.  This process will terminate when we hit
        // the null slot at the end of this run.
        // The test is messy because we are using a circular table.
        {
            int r = hash(item, len);
            if ((i < r && (r <= d || d <= i)) || (r <= d && d <= i)) {
                tab[d] = item;
                tab[d + 1] = tab[i + 1];
                tab[i] = null;
                tab[i + 1] = null;
                d = i;
            }
        }
    }

    /**
     * Removes all of the mappings from this map.
     * The map will be empty after this call returns.
     */
    /*+KEY@ 
      @ also
      @ public normal_behavior
      @   assignable
      @     modCount, size, table[0 .. table.length - (\bigint)1];
      @   ensures
      @     \old(modCount) != modCount &&
      @     \old(table.length) == table.length &&
      @     size == 0 &&
      @     (\forall \bigint i;
      @        0 <= i < table.length;
      @        table[i] == null);
      @*/
    /*+OPENJML@
      @ also
      @ public normal_behavior
      @   assignable
      @     modCount, size, table[0 .. table.length - 1];
      @   ensures
      @     \old(modCount) != modCount &&
      @     \old(table.length) == table.length &&
      @     size == 0 &&
      @     (\forall int i;
      @        0 <= i < table.length;
      @        table[i] == null);
      @*/
    public void clear() {
        modCount++;
        Object[] tab = table;

        /*+KEY@
          @ maintaining
          @   0 <= i && i <= tab.length;
          @ maintaining
          @   (\forall \bigint j; 0 <= j < i; tab[j] == null);
          @ decreasing
          @   tab.length - i;
          @ assignable
          @   tab[0 .. tab.length - (\bigint)1];
          @*/
        for (int i = 0; i < tab.length; i++)
            tab[i] = null;
        size = 0;
    }

    /**
     * Compares the specified object with this map for equality.  Returns
     * <tt>true</tt> if the given object is also a map and the two maps
     * represent identical object-reference mappings.  More formally, this
     * map is equal to another map <tt>m</tt> if and only if
     * <tt>this.entrySet().equals(m.entrySet())</tt>.
     *
     * <p><b>Owing to the reference-equality-based semantics of this map it is
     * possible that the symmetry and transitivity requirements of the
     * <tt>Object.equals</tt> contract may be violated if this map is compared
     * to a normal map.  However, the <tt>Object.equals</tt> contract is
     * guaranteed to hold among <tt>VerifiedIdentityHashMap</tt> instances.</b>
     *
     * @param o object to be compared for equality with this map
     * @return <tt>true</tt> if the specified object is equal to this map
     * @see Object#equals(Object)
     */
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        } else if (o instanceof VerifiedIdentityHashMap) {
            VerifiedIdentityHashMap m = (VerifiedIdentityHashMap) o;
            if (m.size() != size)
                return false;

            Object[] tab = m.table;
            for (int i = 0; i < tab.length; i += 2) {
                Object k = tab[i];
                if (k != null && !containsMapping(k, tab[i + 1]))
                    return false;
            }
            return true;
        } else if (o instanceof Map) {
            Map m = (Map) o;
            return entrySet().equals(m.entrySet());
        } else {
            return false;  // o is not a Map
        }
    }

    /**
     * Returns the hash code value for this map.  The hash code of a map is
     * defined to be the sum of the hash codes of each entry in the map's
     * <tt>entrySet()</tt> view.  This ensures that <tt>m1.equals(m2)</tt>
     * implies that <tt>m1.hashCode()==m2.hashCode()</tt> for any two
     * <tt>VerifiedIdentityHashMap</tt> instances <tt>m1</tt> and <tt>m2</tt>, as
     * required by the general contract of {@link Object#hashCode}.
     *
     * <p><b>Owing to the reference-equality-based semantics of the
     * <tt>Map.Entry</tt> instances in the set returned by this map's
     * <tt>entrySet</tt> method, it is possible that the contractual
     * requirement of <tt>Object.hashCode</tt> mentioned in the previous
     * paragraph will be violated if one of the two objects being compared is
     * an <tt>VerifiedIdentityHashMap</tt> instance and the other is a normal map.</b>
     *
     * @return the hash code value for this map
     * @see Object#equals(Object)
     * @see #equals(Object)
     */
    public int hashCode() {
        int result = 0;
        Object[] tab = table;
        for (int i = 0; i < tab.length; i += 2) {
            Object key = tab[i];
            if (key != null) {
                Object k = unmaskNull(key);
                result += System.identityHashCode(k) ^
                        System.identityHashCode(tab[i + 1]);
            }
        }
        return result;
    }

    /**
     * Returns a shallow copy of this identity hash map: the keys and values
     * themselves are not cloned.
     *
     * @return a shallow copy of this map
     */
    public Object clone() {
        try {
            VerifiedIdentityHashMap m = (VerifiedIdentityHashMap) super.clone();
            m.entrySet = null;
            m.table = table.clone();
            return m;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }

    private abstract class IdentityHashMapIterator implements Iterator {
        int index = (size != 0 ? 0 : table.length); // current slot.
        int expectedModCount = modCount; // to support fast-fail
        int lastReturnedIndex = -1;      // to allow remove()
        boolean indexValid; // To avoid unnecessary next computation
        Object[] traversalTable = table; // reference to main table or copy

        public boolean hasNext() {
            Object[] tab = traversalTable;
            for (int i = index; i < tab.length; i += 2) {
                Object key = tab[i];
                if (key != null) {
                    index = i;
                    return indexValid = true;
                }
            }
            index = tab.length;
            return false;
        }

        protected int nextIndex() {
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            if (!indexValid && !hasNext())
                throw new NoSuchElementException();

            indexValid = false;
            lastReturnedIndex = index;
            index += 2;
            return lastReturnedIndex;
        }

        public void remove() {
            if (lastReturnedIndex == -1)
                throw new IllegalStateException();
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();

            expectedModCount = ++modCount;
            int deletedSlot = lastReturnedIndex;
            lastReturnedIndex = -1;
            // back up index to revisit new contents after deletion
            index = deletedSlot;
            indexValid = false;

            // Removal code proceeds as in closeDeletion except that
            // it must catch the rare case where an element already
            // seen is swapped into a vacant slot that will be later
            // traversed by this iterator. We cannot allow future
            // next() calls to return it again.  The likelihood of
            // this occurring under 2/3 load factor is very slim, but
            // when it does happen, we must make a copy of the rest of
            // the table to use for the rest of the traversal. Since
            // this can only happen when we are near the end of the table,
            // even in these rare cases, this is not very expensive in
            // time or space.

            Object[] tab = traversalTable;
            int len = tab.length;

            int d = deletedSlot;
            Object key = tab[d];
            tab[d] = null;        // vacate the slot
            tab[d + 1] = null;

            // If traversing a copy, remove in real table.
            // We can skip gap-closure on copy.
            if (tab != VerifiedIdentityHashMap.this.table) {
                VerifiedIdentityHashMap.this.remove(key);
                expectedModCount = modCount;
                return;
            }

            size--;

            Object item;
            for (int i = nextKeyIndex(d, len); (item = tab[i]) != null;
                 i = nextKeyIndex(i, len)) {
                int r = hash(item, len);
                // See closeDeletion for explanation of this conditional
                if ((i < r && (r <= d || d <= i)) ||
                        (r <= d && d <= i)) {

                    // If we are about to swap an already-seen element
                    // into a slot that may later be returned by next(),
                    // then clone the rest of table for use in future
                    // next() calls. It is OK that our copy will have
                    // a gap in the "wrong" place, since it will never
                    // be used for searching anyway.

                    if (i < deletedSlot && d >= deletedSlot &&
                            traversalTable == VerifiedIdentityHashMap.this.table) {
                        int remaining = len - deletedSlot;
                        Object[] newTable = new Object[remaining];
                        System.arraycopy(tab, deletedSlot,
                                newTable, 0, remaining);
                        traversalTable = newTable;
                        index = 0;
                    }

                    tab[d] = item;
                    tab[d + 1] = tab[i + 1];
                    tab[i] = null;
                    tab[i + 1] = null;
                    d = i;
                }
            }
        }
    }

    private class KeyIterator extends IdentityHashMapIterator {
        @SuppressWarnings("unchecked")
        public java.lang.Object next() {
            return (java.lang.Object) unmaskNull(traversalTable[nextIndex()]);
        }
    }

    private class ValueIterator extends IdentityHashMapIterator {
        @SuppressWarnings("unchecked")
        public java.lang.Object next() {
            return (java.lang.Object) traversalTable[nextIndex() + 1];
        }
    }

    private class EntryIterator
            extends IdentityHashMapIterator {
        private Entry lastReturnedEntry = null;

        public Map.Entry next() {
            lastReturnedEntry = new Entry(nextIndex());
            return lastReturnedEntry;
        }

        public void remove() {
            lastReturnedIndex =
                    ((null == lastReturnedEntry) ? -1 : lastReturnedEntry.index);
            super.remove();
            lastReturnedEntry.index = lastReturnedIndex;
            lastReturnedEntry = null;
        }

        private class Entry implements Map.Entry {
            private int index;

            private Entry(int index) {
                this.index = index;
            }

            @SuppressWarnings("unchecked")
            public java.lang.Object getKey() {
                checkIndexForEntryUse();
                return (java.lang.Object) unmaskNull(traversalTable[index]);
            }

            @SuppressWarnings("unchecked")
            public java.lang.Object getValue() {
                checkIndexForEntryUse();
                return (java.lang.Object) traversalTable[index + 1];
            }

            @SuppressWarnings("unchecked")
            public java.lang.Object setValue(java.lang.Object value) {
                checkIndexForEntryUse();
                java.lang.Object oldValue = (java.lang.Object) traversalTable[index + 1];
                traversalTable[index + 1] = value;
                // if shadowing, force into main table
                if (traversalTable != VerifiedIdentityHashMap.this.table)
                    put((java.lang.Object) traversalTable[index], value);
                return oldValue;
            }

            public boolean equals(Object o) {
                if (index < 0)
                    return super.equals(o);

                if (!(o instanceof Map.Entry))
                    return false;
                Map.Entry e = (Map.Entry) o;
                return (e.getKey() == unmaskNull(traversalTable[index]) &&
                        e.getValue() == traversalTable[index + 1]);
            }

            public int hashCode() {
                if (lastReturnedIndex < 0)
                    return super.hashCode();

                return (System.identityHashCode(unmaskNull(traversalTable[index])) ^
                        System.identityHashCode(traversalTable[index + 1]));
            }

            public String toString() {
                if (index < 0)
                    return super.toString();

                return (unmaskNull(traversalTable[index]) + "="
                        + traversalTable[index + 1]);
            }

            private void checkIndexForEntryUse() {
                if (index < 0)
                    throw new IllegalStateException("Entry was removed");
            }
        }
    }

    // Views

    /**
     * This field is initialized to contain an instance of the entry set
     * view the first time this view is requested.  The view is stateless,
     * so there's no reason to create more than one.
     */
    private /*@ spec_public nullable @*/ transient Set entrySet = null;

    /**
     * Returns an identity-based set view of the keys contained in this map.
     * The set is backed by the map, so changes to the map are reflected in
     * the set, and vice-versa.  If the map is modified while an iteration
     * over the set is in progress, the results of the iteration are
     * undefined.  The set supports element removal, which removes the
     * corresponding mapping from the map, via the <tt>Iterator.remove</tt>,
     * <tt>Set.remove</tt>, <tt>removeAll</tt>, <tt>retainAll</tt>, and
     * <tt>clear</tt> methods.  It does not support the <tt>add</tt> or
     * <tt>addAll</tt> methods.
     *
     * <p><b>While the object returned by this method implements the
     * <tt>Set</tt> interface, it does <i>not</i> obey <tt>Set's</tt> general
     * contract.  Like its backing map, the set returned by this method
     * defines element equality as reference-equality rather than
     * object-equality.  This affects the behavior of its <tt>contains</tt>,
     * <tt>remove</tt>, <tt>containsAll</tt>, <tt>equals</tt>, and
     * <tt>hashCode</tt> methods.</b>
     *
     * <p><b>The <tt>equals</tt> method of the returned set returns <tt>true</tt>
     * only if the specified object is a set containing exactly the same
     * object references as the returned set.  The symmetry and transitivity
     * requirements of the <tt>Object.equals</tt> contract may be violated if
     * the set returned by this method is compared to a normal set.  However,
     * the <tt>Object.equals</tt> contract is guaranteed to hold among sets
     * returned by this method.</b>
     *
     * <p>The <tt>hashCode</tt> method of the returned set returns the sum of
     * the <i>identity hashcodes</i> of the elements in the set, rather than
     * the sum of their hashcodes.  This is mandated by the change in the
     * semantics of the <tt>equals</tt> method, in order to enforce the
     * general contract of the <tt>Object.hashCode</tt> method among sets
     * returned by this method.
     *
     * @return an identity-based set view of the keys contained in this map
     * @see Object#equals(Object)
     * @see System#identityHashCode(Object)
     */
    public Set keySet() {
        Set ks = keySet;
        if (ks != null)
            return ks;
        else
            return keySet = new KeySet();
    }

    private class KeySet extends AbstractSet {
        public Iterator iterator() {
            return new KeyIterator();
        }

        public int size() {
            return size;
        }

        public boolean contains(Object o) {
            return containsKey(o);
        }

        public boolean remove(Object o) {
            int oldSize = size;
            VerifiedIdentityHashMap.this.remove(o);
            return size != oldSize;
        }

        /*
         * Must revert from AbstractSet's impl to AbstractCollection's, as
         * the former contains an optimization that results in incorrect
         * behavior when c is a smaller "normal" (non-identity-based) Set.
         */
        public boolean removeAll(Collection c) {
            boolean modified = false;
            for (Iterator i = iterator(); i.hasNext(); ) {
                if (c.contains(i.next())) {
                    i.remove();
                    modified = true;
                }
            }
            return modified;
        }

        public void clear() {
            VerifiedIdentityHashMap.this.clear();
        }

        public int hashCode() {
            int result = 0;
            for (java.lang.Object key : this)
                result += System.identityHashCode(key);
            return result;
        }
    }

    /**
     * Returns a {@link Collection} view of the values contained in this map.
     * The collection is backed by the map, so changes to the map are
     * reflected in the collection, and vice-versa.  If the map is
     * modified while an iteration over the collection is in progress,
     * the results of the iteration are undefined.  The collection
     * supports element removal, which removes the corresponding
     * mapping from the map, via the <tt>Iterator.remove</tt>,
     * <tt>Collection.remove</tt>, <tt>removeAll</tt>,
     * <tt>retainAll</tt> and <tt>clear</tt> methods.  It does not
     * support the <tt>add</tt> or <tt>addAll</tt> methods.
     *
     * <p><b>While the object returned by this method implements the
     * <tt>Collection</tt> interface, it does <i>not</i> obey
     * <tt>Collection's</tt> general contract.  Like its backing map,
     * the collection returned by this method defines element equality as
     * reference-equality rather than object-equality.  This affects the
     * behavior of its <tt>contains</tt>, <tt>remove</tt> and
     * <tt>containsAll</tt> methods.</b>
     */
    public Collection values() {
        Collection vs = values;
        if (vs != null)
            return vs;
        else
            return values = new Values();
    }

    private class Values extends AbstractCollection {
        public Iterator iterator() {
            return new ValueIterator();
        }

        public int size() {
            return size;
        }

        public boolean contains(Object o) {
            return containsValue(o);
        }

        public boolean remove(Object o) {
            for (Iterator i = iterator(); i.hasNext(); ) {
                if (i.next() == o) {
                    i.remove();
                    return true;
                }
            }
            return false;
        }

        public void clear() {
            VerifiedIdentityHashMap.this.clear();
        }
    }

    /**
     * Returns a {@link Set} view of the mappings contained in this map.
     * Each element in the returned set is a reference-equality-based
     * <tt>Map.Entry</tt>.  The set is backed by the map, so changes
     * to the map are reflected in the set, and vice-versa.  If the
     * map is modified while an iteration over the set is in progress,
     * the results of the iteration are undefined.  The set supports
     * element removal, which removes the corresponding mapping from
     * the map, via the <tt>Iterator.remove</tt>, <tt>Set.remove</tt>,
     * <tt>removeAll</tt>, <tt>retainAll</tt> and <tt>clear</tt>
     * methods.  It does not support the <tt>add</tt> or
     * <tt>addAll</tt> methods.
     *
     * <p>Like the backing map, the <tt>Map.Entry</tt> objects in the set
     * returned by this method define key and value equality as
     * reference-equality rather than object-equality.  This affects the
     * behavior of the <tt>equals</tt> and <tt>hashCode</tt> methods of these
     * <tt>Map.Entry</tt> objects.  A reference-equality based <tt>Map.Entry
     * e</tt> is equal to an object <tt>o</tt> if and only if <tt>o</tt> is a
     * <tt>Map.Entry</tt> and <tt>e.getKey()==o.getKey() &amp;&amp;
     * e.getValue()==o.getValue()</tt>.  To accommodate these equals
     * semantics, the <tt>hashCode</tt> method returns
     * <tt>System.identityHashCode(e.getKey()) ^
     * System.identityHashCode(e.getValue())</tt>.
     *
     * <p><b>Owing to the reference-equality-based semantics of the
     * <tt>Map.Entry</tt> instances in the set returned by this method,
     * it is possible that the symmetry and transitivity requirements of
     * the {@link Object#equals(Object)} contract may be violated if any of
     * the entries in the set is compared to a normal map entry, or if
     * the set returned by this method is compared to a set of normal map
     * entries (such as would be returned by a call to this method on a normal
     * map).  However, the <tt>Object.equals</tt> contract is guaranteed to
     * hold among identity-based map entries, and among sets of such entries.
     * </b>
     *
     * @return a set view of the identity-mappings contained in this map
     */
    public Set entrySet() {
        Set es = entrySet;
        if (es != null)
            return es;
        else
            return entrySet = new EntrySet();
    }

    private class EntrySet extends AbstractSet {
        public Iterator iterator() {
            return new EntryIterator();
        }

        public boolean contains(Object o) {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry entry = (Map.Entry) o;
            return containsMapping(entry.getKey(), entry.getValue());
        }

        public boolean remove(Object o) {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry entry = (Map.Entry) o;
            return removeMapping(entry.getKey(), entry.getValue());
        }

        public int size() {
            return size;
        }

        public void clear() {
            VerifiedIdentityHashMap.this.clear();
        }

        /*
         * Must revert from AbstractSet's impl to AbstractCollection's, as
         * the former contains an optimization that results in incorrect
         * behavior when c is a smaller "normal" (non-identity-based) Set.
         */
        public boolean removeAll(Collection c) {
            boolean modified = false;
            for (Iterator i = iterator(); i.hasNext(); ) {
                if (c.contains(i.next())) {
                    i.remove();
                    modified = true;
                }
            }
            return modified;
        }

        public Object[] toArray() {
            int size = size();
            Object[] result = new Object[size];
            Iterator it = iterator();
            for (int i = 0; i < size; i++)
                result[i] = new AbstractMap.SimpleEntry(((java.util.Map.Entry) it.next()));
            return result;
        }

        @SuppressWarnings("unchecked")
        public java.lang.Object[] toArray(java.lang.Object[] a) {
            int size = size();
            if (a.length < size)
                a = (java.lang.Object[]) java.lang.reflect
                        .Array.newInstance(a.getClass().getComponentType(), size);
            Iterator it = iterator();
            for (int i = 0; i < size; i++)
                a[i] = (java.lang.Object) new AbstractMap.SimpleEntry(((java.util.Map.Entry) it.next()));
            if (a.length > size)
                a[size] = null;
            return a;
        }
    }


//    private static final long serialVersionUID = 8188218128353913216L;
//
//    /**
//     * Saves the state of the <tt>VerifiedIdentityHashMap</tt> instance to a stream
//     * (i.e., serializes it).
//     *
//     * @serialData The <i>size</i> of the HashMap (the number of key-value
//     *          mappings) (<tt>int</tt>), followed by the key (Object) and
//     *          value (Object) for each key-value mapping represented by the
//     *          VerifiedIdentityHashMap.  The key-value mappings are emitted in no
//     *          particular order.
//     */
//    private void writeObject(java.io.ObjectOutputStream s)
//            throws java.io.IOException  {
//        // Write out and any hidden stuff
//        s.defaultWriteObject();
//
//        // Write out size (number of Mappings)
//        s.writeInt(size);
//
//        // Write out keys and values (alternating)
//        Object[] tab = table;
//        for (int i = 0; i < tab.length; i += 2) {
//            Object key = tab[i];
//            if (key != null) {
//                s.writeObject(unmaskNull(key));
//                s.writeObject(tab[i + 1]);
//            }
//        }
//    }

//    /**
//     * Reconstitutes the <tt>VerifiedIdentityHashMap</tt> instance from a stream (i.e.,
//     * deserializes it).
//     */
//    private void readObject(java.io.ObjectInputStream s)
//            throws java.io.IOException, ClassNotFoundException  {
//        // Read in any hidden stuff
//        s.defaultReadObject();
//
//        // Read in size (number of Mappings)
//        int size = s.readInt();
//        if (size < 0)
//            throw new java.io.StreamCorruptedException
//                    ("Illegal mappings count: " + size);
//        int cap = capacity(size);
//        SharedSecrets.getJavaOISAccess().checkArray(s, Object[].class, cap);
//        init(cap);
//
//        // Read the keys and values, and put the mappings in the table
//        for (int i=0; i<size; i++) {
//            @SuppressWarnings("unchecked")
//            K key = (K) s.readObject();
//            @SuppressWarnings("unchecked")
//            V value = (V) s.readObject();
//            putForCreate(key, value);
//        }
//    }

//    /**
//     * The put method for readObject.  It does not resize the table,
//     * update modCount, etc.
//     */
//    private void putForCreate(K key, V value)
//            throws java.io.StreamCorruptedException
//    {
//        Object k = maskNull(key);
//        Object[] tab = table;
//        int len = tab.length;
//        int i = hash(k, len);
//
//        Object item;
//        while ( (item = tab[i]) != null) {
//            if (item == k)
//                throw new java.io.StreamCorruptedException();
//            i = nextKeyIndex(i, len);
//        }
//        tab[i] = k;
//        tab[i + 1] = value;
//    }
}