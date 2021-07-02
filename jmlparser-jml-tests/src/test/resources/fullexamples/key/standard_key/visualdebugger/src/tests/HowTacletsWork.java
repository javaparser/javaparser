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

package tests;

/**
 * The Class HowTacletsWork.
 * 
 * Used to demonstrate how taclets in the KeY-System work, 
 * respectivly in the Visual Debugger.
 * For this purpose Debug.sep(int intlit) statements are inserted
 * manually. This part below is commented out to avoid compiler errors.
 * 
 */

public class HowTacletsWork {
	//unimportant
	public static void main(String[] args){
		HowTacletsWork htw = new HowTacletsWork();
		int[] i = {3,4,5};
		//System.out.println(htw.middle(i));
	}
	
public static void sep(int lit){/** Empty method stub */}
	
	public static int sep(int lit, int exp){
		return exp;
	}
	public static boolean sep(int lit, boolean exp){
		return exp;
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
	sep(1);
		int max = values[sep(8,0)];
		sep(2);
		int i = 0;
		sep(3);
		while (sep(9, i < values.length) ) {
			sep(4);
			int j = values[sep(10,i++)];
			sep(5);
			if (sep(11,j > max)) {
			sep(6);
				max = j;
			}
		}sep(7);
		return max;
	}

	/**
	 * Middle.
	 * 
	 * Returns the middle Value of a given array.
	 * For demo purpose.
	 * 
	 * @param myArray
	 *            the integer array
	 * 
	 * @return the integer in the middle of the array.
	 * 
	 *
	 */
	/*@ public normal_behavior ensures true; @*/
	
		public int middle(int[] myArray) {
		sep(12);
		int i = myArray.length / 2;
		sep(13);
		return myArray[sep(14,i)];
	}
}
/**
  
 Here the Debug.sep(); statements are inserted.
 
package tests;

public class HowTacletsWork {

	

	
}
*/
