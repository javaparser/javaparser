// Copyright (C) 2011 Daniel Bruns
// Published under Modified BSD License
// See LICENSE for details.

package vacid0.redblacktree;

/**
 * Mutable map interface without data structure exposure.
 * Specifications are in JML*, i.e. an extension to JML with dynamic frames
 * (see <a href="http://www.springerlink.com/index/74K70022344R344R.pdf">
 * Ioannis Kassios: <i>Dynamic frames: Support for framing, dependencies and sharing without restrictions</i></a> and
 * <a href="http://books.google.com/books?hl=en&lr=&id=AJlGLueHYzsC&oi=fnd&pg=PA1&dq=wei%C3%9F+deductive+verification&ots=rMfF5Wn9yd&sig=SL4830OoAPFO3WZd8ZypRrlwJHE">
 * Benjamin Wei&szlig;: <i>Deductive verification of object-oriented software: dynamic frames, dynamic logic and predicate abstraction</i></a>)
 * @author bruns
 *
 */
public interface AbstractMap{

    /*@ protected model instance int defaultValue;
      @ protected model instance \seq contents;
      @ protected model instance \locset footprint;
      @*/
    
    /*@ protected model instance boolean isEmpty;
      @ protected represents isEmpty = (\forall int i; 0 <= i && i < contents.length; contents[i] == defaultValue);
      @*/

    //@ initially isEmpty;
    
    /*@ accessible defaultValue: \nothing;
      @ accessible \inv : footprint;
      @ accessible contents : footprint;
      @ accessible footprint : footprint;
      @*/

    /** Set the value of key; add it if it is not in the map yet */
    /*@ public normal_behavior
      @ requires 0 <= key && key < contents.length;
      @ ensures contents == \seq_put(\old(contents),key,value);
      @ ensures \new_elems_fresh(footprint);
      @ assignable footprint;
      @*/
    public void replace (int key, int value);

    /** Remove key from the map */
    /*@ public normal_behavior
      @ requires 0 <= key && key < contents.length;
      @ ensures contents == \seq_put(\old(contents),key,defaultValue);
      @ ensures \new_elems_fresh(footprint);
      @ assignable footprint;
      @*/
    public void remove (int key);

    /** Lookup the key; if it is not in the map, return the default value */
    /*@ public normal_behavior
      @ requires 0 <= key && key < contents.length;
      @ ensures \result == contents[key];
      @ accessible footprint;
      @*/
    public /*@ pure @*/ int lookup (int key);
}
