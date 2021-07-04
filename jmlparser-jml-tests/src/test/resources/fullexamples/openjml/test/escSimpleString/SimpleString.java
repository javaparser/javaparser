/*
 * Fall 2013 CSCI181G - Homework 6
 * Static and Runtime Checking
 */

package esc;


/**
 * A trivial string class that supports initialization, 
 * concatenation and the substring operation.
 * @author Daniel M. Zimmerman
 * @author YOUR NAME HERE
 * @version 2013-11-04
 */
@org.jmlspecs.annotation.CodeBigintMath @org.jmlspecs.annotation.SpecBigintMath
public class SimpleString {
  /*
   * The class should have a history constraint about the fact
   * that it is immutable ("final" on the array isn't quite good enough).
   */
  
  // Instance Fields
  
  /**
   * The character data of this SimpleString.
   */
    private /*@ spec_public nullable */ char[] my_chars;  
    private /*@ spec_public nullable */ int[] my_ints;
    private /*@ spec_public nullable */ Object[] my_Objects;  
    private /*@ spec_public nullable */ Integer[] my_Integers;  
  
  // Constructors
  
    /**
     * Constructs a new SimpleString with the contents of the specified
     * array of characters in the order they appear in the array.
     * 
     * @param the_array The array of characters.
     */
    //@ ensures (\forall int i; 0 <= i && i < my_chars.length; my_chars[i] == the_array[i]);
    public SimpleString(final /*@ non_null */ char[] the_array) {
        // @ assert the_array != null;
        my_chars = new char[the_array.length];
        System.arraycopy(the_array, 0, my_chars, 0, the_array.length);
    }

    /**
     * Constructs a new SimpleString with the contents of the specified
     * array of ints in the order they appear in the array.
     * 
     * @param the_array The array of ints.
     */
    //@ ensures (\forall int i; 0 <= i && i < my_ints.length; my_ints[i] == the_array[i]);
    public SimpleString(final /*@ non_null */ int[] the_array) {
        my_ints = new int[the_array.length];
        System.arraycopy(the_array, 0, my_ints, 0, the_array.length);
    }

    /**
     * Constructs a new SimpleString with the contents of the specified
     * array of ints in the order they appear in the array.
     * 
     * @param the_array The array of ints.
     */
    //@ ensures my_Objects.length == the_array.length;
    //@ ensures (\forall int i; 0 <= i && i < my_Objects.length; my_Objects[i] == the_array[i]);
    public SimpleString(final /*@ non_null */ Object[] the_array) {
        my_Objects = new Object[the_array.length];
        System.arraycopy(the_array, 0, my_Objects, 0, the_array.length);
    }

    //@ ensures my_Integers.length == the_array.length;
    //@ ensures (\forall int i; 0 <= i && i < my_Integers.length; my_Integers[i] == the_array[i]);
    public SimpleString(final /*@ non_null */ Integer[] the_array) {
        my_Integers = new Integer[the_array.length];
        System.arraycopy(the_array, 0, my_Integers, 0, the_array.length);
    }

}
