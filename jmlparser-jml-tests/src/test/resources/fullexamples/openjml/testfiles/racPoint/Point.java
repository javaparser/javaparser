/*  NOTE: This submitted as a test case because RAC crashes when it encounters a model method in the java.lang.Math spec, which doee not have a real counterpart because java.lang.Math is not RAC-compiled.
 * Two-Dimensional Points
 * Fall 2013 CSCI181F
 * Daniel M. Zimmerman
 */

/**
 * A point in the Euclidean plane.
 * 
 * @author Daniel M. Zimmerman
 * @version 2013-10-31
 */
public class Point {
    public static enum CoordinateSystem {
        CARTESIAN, POLAR
    }
  /**
   * The margin of error for double-precision arithmetic.
   */
  public static final double ERROR_MARGIN = 1E-10;
  
  /**
   * The format string for computing hash codes that will
   * work with the error margin.
   */
  public static final String ERROR_FORMAT = "%.10f";
  
  /**
   * The x-coordinate.
   */
  private final double my_x;
  
  /**
   * The y-coordinate.
   */
  private final double my_y;
  
  /*@ requires the_system == CoordinateSystem.CARTESIAN | 
               the_system == CoordinateSystem.POLAR; */
  /*@ requires the_system == CoordinateSystem.POLAR ==> 
                 0 <= coord_1 & 0 <= coord_2 & coord_2 < 2 * Math.PI; */
  //@ requires isFinite(coord_1) & isFinite(coord_2);
  /*@ ensures the_system == CoordinateSystem.CARTESIAN ==>
                x() == coord_1 & y() == coord_2; */
  /*@ ensures the_system == CoordinateSystem.POLAR ==>
                approxEquals(rho(), coord_1) & approxEquals(theta(), coord_2); */
  /**
   * Your Cartesian coordinates are (the_x, the_y)!
   * Your polar coordinates are (the_rho, the_theta)!
   * 
   * Constructs a Point with the specified coordinates in
   * the specified coordinate system.
   * 
   * @param coord_1 The x-coordinate or rho.
   * @param coord_2 The y-coordinate or theta.
   * @param the_system The coordinate system.
   */
  public Point(final double coord_1, final double coord_2,
               final CoordinateSystem the_system)  {
    switch (the_system) {
      case CARTESIAN:
        my_x = coord_1;
        my_y = coord_2;
        break;
        
      case POLAR:
        my_x = coord_1 * Math.cos(coord_2);
        my_y = coord_1 * Math.sin(coord_2);
        break;
        
      default:
        throw new IllegalArgumentException
        ("I don't know coordinate system " + the_system);
    }
  }
  
  /**
   * Compares two numbers for approximate equivalence. They
   * must be within ERROR_MARGIN of each other.
   * 
   * @param number_1 The first number.
   * @param number_2 The second number.
   * @return true if the two specified numbers are approximately
   * equivalent, false otherwise.
   */
  //@ ensures \result <==> Math.abs(number_1 - number_2) < ERROR_MARGIN;
  public static /*@ pure */ boolean approxEquals(final double number_1,
                                                 final double number_2) {
    return Math.abs(number_1 - number_2) < ERROR_MARGIN;
  } 
  
  /*@ ensures \result <==> the_number != Double.NEGATIVE_INFINITY &
                           the_number != Double.POSITIVE_INFINITY &
                           !Double.isNaN(the_number); */
  /**
   * Checks a double-precision floating point number for finiteness.
   * 
   * @param the_number The number to check.
   * @return true if the_number is finite, false otherwise.
   */
  public static /*@ pure */ boolean isFinite(final double the_number) {
    return the_number != Double.NEGATIVE_INFINITY &&
           the_number != Double.POSITIVE_INFINITY &&
           !Double.isNaN(the_number);
  }
  
  /**
   * Normalizes an angle to be between 0 (inclusive) and 2 * Math.PI
   * (exclusive).
   * 
   * @param the_angle The angle.
   * @return The normalized angle.
   */
  public static /*@ pure */ double normalize(final double the_angle) {
    double result = the_angle;
    // repeatedly subtract 2 * Math.PI until we're less than 2 * Math.PI
    while (result > 2 * Math.PI) {
      result = result - 2 * Math.PI;
    }
    // repeatedly add 2 * Math.PI until we're greater than 0
    while (result <= 0) {
      result = result + 2 * Math.PI;
    }
    return result; // should be normalized
  }
  
  /**
   * @return What is your x-coordinate?
   */
  public /*@ pure */ double x() {
    return my_x;
  }
  
  /**
   * @return What is your y-coordinate?
   */
  public /*@ pure */ double y() {
    return my_y;
  }
  
  /**
   * @return What is your rho?
   */
  public /*@ pure */ double rho() {
    return Math.sqrt(my_x * my_x + my_y * my_y);
  }
  
  /**
   * @return What is your theta?
   */
  public /*@ pure */ double theta() {
    return Math.atan2(my_y, my_x);
  }
  
  /**
   * A main method to demonstrate a JML error.
   */
  public static void main(final String[] the_args) {
    new Point(0.0, 0.0, CoordinateSystem.CARTESIAN).rho();
  }
}
