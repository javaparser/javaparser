/*
 * Extended Static Checking Exercise
 * Fall 2013 CSCI181F - Verification-centric Software Engineering
 * Daniel M. Zimmerman
 */

/**
 * A class that implements a growable array of objects, based
 * on an old implementation of java.util.Vector - original source
 * by Lee Boynton and Jonathan Payne, Sun Microsystems.
 * 
 * @author Daniel M. Zimmerman
 * @version 2013-10-24 (based on v1.38, 12/18/97)
 */
public class Vector {
  //@ public invariant my_element_data != null;
  //@ public invariant my_element_count >= 0;
  //@ public invariant my_element_count <= my_element_data.length;
  //@ public invariant my_capacity_increment > 0;
  /**
   * The array buffer into which the components of the vector are 
   * stored. The capacity of the vector is the length of this array buffer.
   *
   * @since   JDK1.0
   */
    //@ public invariant \elemtype(\typeof(my_element_data)) == \type(Object);
  private /*@ spec_public */ Object[] my_element_data;

  /**
   * The number of valid components in the vector. 
   *
   * @since   JDK1.0
   */
  private /*@ spec_public */ int my_element_count;

  /**
   * The amount by which the capacity of the vector is automatically 
   * incremented when its size becomes greater than its capacity. If 
   * the capacity increment is <code>0</code>, the capacity of the 
   * vector is doubled each time it needs to grow. 
   *
   * @since   JDK1.0
   */
  private /*@ spec_public */ final int my_capacity_increment;

  /**
   * Constructs an empty vector with the specified initial capacity and
   * capacity increment. 
   *
   * @param   the_initial_capacity     the initial capacity of the vector.
   * @param   the_capacity_increment   the amount by which the capacity is
   *                                   increased when the vector overflows.
   * @since   JDK1.0
   */
  //@ requires the_initial_capacity >= 0 && the_capacity_increment > 0;
  public Vector(final int the_initial_capacity, final int the_capacity_increment) {
    my_element_data = new Object[the_initial_capacity];
    my_capacity_increment = the_capacity_increment;
  }

  /**
   * Adds an element to the vector.
   * 
   * @param the_object The element to add.
   */
  public final synchronized void add(final Object the_object) {
    if (my_element_count >= my_element_data.length) {
      // create a new array
      final Object[] new_data = new Object[my_element_count + my_capacity_increment]; // ERROR - could be negative under Java math
      //@ ghost Object[] nd = new_data;
      //@ loop_invariant 0 <= i && i <= my_element_count && new_data == nd;
      //@ decreases my_element_count - i;
      for (int i = 0; i < my_element_count; i++) {
        new_data[i] = my_element_data[i];
      }
      my_element_data = new_data;
    }
    my_element_data[my_element_count++] = the_object;
  }
  
  /**
   * Copies the components of this vector into the specified array. 
   * The array must be big enough to hold all the objects in this  vector.
   *
   * @param   the_array   the array into which the components get copied.
   * @since   JDK1.0
   */
  public final synchronized void copyInto(final Object[] the_array) {
    int i = my_element_count;
    //@ loop_invariant 0 <= i && i <= my_element_count;
    //@ decreases i;
    while (i-- > 0) {
      the_array[i] = my_element_data[i]; // ERROR _ don't know size of the_array - i might be too big; ERROR - don't know the runtime type of the_array
    }
  }
   
  /**
   * Searches for the first occurrence of the given argument, beginning the
   * search at <code>index</code>, and testing for equality using the
   * <code>equals</code> method.
   * 
   * @param the_elem an object.
   * @param the_index the index to start searching from.
   * @return the index of the first occurrence of the object argument in this
   *         vector at position <code>index</code> or later in the vector;
   *         returns <code>-1</code> if the object is not found.
   * @see java.lang.Object#equals(java.lang.Object)
   * @since JDK1.0   
   */
  public final synchronized int indexOf(final Object the_elem, final int the_index) {
    //@ loop_invariant the_index == i || (the_index <= i && i <= my_element_count);
    //@ decreases my_element_count - i;
    for (int i = the_index; i < my_element_count; i++) {
      if (the_elem.equals(my_element_data[i])) {   // the_index might be negative
        return i;
      }
    }
    return -1;
  }

  /**
   * Returns the component at the specified index.
   * 
   * @param the_index an index into this vector.
   * @return the component at the specified index.
   * @exception ArrayIndexOutOfBoundsException if an invalid index was given.
   * @since JDK1.0
   */  //@ requires the_index >= 0;
  public final synchronized Object elementAt(final int the_index) 
    throws ArrayIndexOutOfBoundsException {
    if (the_index >= my_element_count) {
      throw new ArrayIndexOutOfBoundsException(the_index + " >= " + my_element_count);
    }
    try {
      return my_element_data[the_index];
    } catch (final ArrayIndexOutOfBoundsException e) {
      throw new ArrayIndexOutOfBoundsException(the_index + " < 0");
    }
  }

}