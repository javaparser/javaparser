/*
 * Fall 2013 CSCI181G - Homework 6
 * Static and Runtime Checking
 */

package esc;

/**
 * A trivial string class that supports initialization, 
 * concatenation and the substring operation.
 * 
 * @author Daniel M. Zimmerman
 * @author YOUR NAME HERE
 * @version 2013-11-04
 */
public class SimpleString {
  /*
   * The class should have a history constraint about the fact
   * that it is immutable ("final" on the array isn't quite good enough).
   */
  
  // Instance Fields
  
  /**
   * The character data of this SimpleString.
   */
  private final char[] my_chars;  
  //@ in chars;
  //@ public model char[] chars; 
  //@ private represents chars = my_chars;
  
  // Constructors
  
  /**
   * Constructs a new SimpleString with the contents of the specified
   * array of characters in the order they appear in the array.
   * 
   * @param the_chars The array of characters.
   */
  //@ ensures (\forall int i; 0 <= i && i < chars.length; chars[i] == the_chars[i]);
  //@ assignable chars;
  public SimpleString(final char[] the_chars) {
    my_chars = new char[the_chars.length];
    //@ maintaining (\forall int j; 0 <= j && j < i; my_chars[j] == the_chars[j]);
    //@ maintaining 0 <= i && i <= my_chars.length;
    //@ decreasing my_chars.length - i;
    for (int i = 0; i < my_chars.length; i++) {
      my_chars[i] = the_chars[i];
    }
  }
}
