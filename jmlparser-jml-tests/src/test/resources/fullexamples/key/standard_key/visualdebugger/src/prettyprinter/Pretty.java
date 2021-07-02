// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package prettyprinter;

import java.util.Random;

/**
 * The Class Pretty.
 * 
 * Created to expose when displayed branch conditions become unreadable in the
 * Visual Debugger.
 */
public class Pretty {

	/** The my array. */
	int[] myArray;

	/**
	 * The main method.
	 * 
	 * @param args
	 *            the arguments
	 */
	public static void main(String[] args) {

		Pretty pretty = new Pretty();
		int[] i = pretty.initMyArray(50);
		System.out.println(pretty.simpleDemo2(pretty.randomValue(i)));

	}

	/**
	 * Complex Demo.
	 * 
	 * This method creates a branched execution tree to show malformed
	 * branchconditions, i.e. not readable for humans. A randomly initialized
	 * integer array is used to build up a complex structure.
	 * 
	 * @return the int
	 * 
	 * required minimal jml spec to make the VD work
	 */
	/*@ public normal_behavior requires true; ensures true; @*/
	public int complexDemo() {

		int result = 0;

		if (max(myArray) < 20) {
			result = 10;
		} else {

			if (max(myArray) < 30) {
				result = 20;
			} else {

				if (max(myArray) < 40) {
					result = 30;
				} else {

					if (max(myArray) < 50)
						result = 40;

				}
			}
		}

		if (max(myArray) > 90) {
			result = 80;
		} else {
			if (max(myArray) > 80) {
				result = 70;
			} else {
				if (max(myArray) > 70) {
					result = 60;
				} else {
					if (max(myArray) > 60)
						result = 50;
				}

			}
		}
		return result;
	}
	/**
	 * Simple Demo 2.
	 * 
	 * More or less the same as simpleDemo() with a random
	 * T 
	 * @return the int
	 * 
	 * required minimal jml spec to make the VD work
	 */
	/*@ public normal_behavior requires true; ensures true; @*/
	public int simpleDemo2(int j) {

		int result = 0;

		if (j < 20) {
			result = 10;
		} else {

			if (j < 30) {
				result = 20;
			} else {

				if (j < 40) {
					result = 30;
				} else {

					if (j < 50)
						result = 40;

				}
			}
		}

		if (j > 90) {
			result = 80;
		} else {
			if (j > 80) {
				result = 70;
			} else {
				if (j > 70) {
					result = 60;
				} else {
					if (j > 60)
						result = 50;
				}

			}
		}
		return result;
	}

	/**
	 * Simple Demo.
	 * 
	 * This method creates a branched execution tree to show malformed
	 * branchconditions, i.e. not readable for humans.
	 * 
	 * @param i -
	 *            a integer
	 * 
	 * @return the int
	 * 
	 * required minimal jml spec to make the VD work:
	 */
	/*@ public normal_behavior requires true; ensures true; @*/
	public int simpleDemo(int i) {

		int result = 0;

		if (i < 20) {
			result = 10;
		} else {

			if (i < 30) {
				result = 20;
			} else {

				if (i < 40) {
					result = 30;
				} else {

					if (i < 50)
						result = 40;

				}
			}
		}

		if (i > 90) {
			result = 80;
		} else {
			if (i > 80) {
				result = 70;
			} else {
				if (i > 70) {
					result = 60;
				} else {
					if (i > 60)
						result = 50;
				}

			}
		}
		return result;
	}

	// some helper methods
	/**
	 * Inits myArray.
	 * 
	 * @param max
	 *            the upper bound for the array values
	 * 
	 * @return the int[]
	 */
	public int[] initMyArray(int max) {

		myArray = new int[10];
		Random nextValue = new Random();
		for (int i = 0; i < 10; i++) {
			myArray[i] = nextValue.nextInt(max);
		}
		return myArray;
	}

	/**
	 * Max.
	 * 
	 * Returns the maximum value of an array.
	 * 
	 * @param values
	 *            the array
	 * 
	 * @return the int
	 * 
	 */
	/*@ public normal_behavior ensures true; @*/
	public int max(int[] values) {

		int max = values[0];
		int i = 0;
		while (i < values.length) {
			int j = values[i++];
			if (j > max) {
				max = j;
			}
		}
		return max;
	}
	/**
	 * randomValue.
	 * 
	 * Returns a random value out of a given array.
	 * 
	 * @param values
	 *            the array
	 * 
	 * @return the int
	 * 
	 */
	public int randomValue(int[] values) {

		Random position = new Random();
		return values[position.nextInt(values.length-1)];
	}
}
