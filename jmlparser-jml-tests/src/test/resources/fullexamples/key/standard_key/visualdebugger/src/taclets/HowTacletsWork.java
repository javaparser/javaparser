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
		System.out.println(htw.middle(i));
	}
	/**
	 * Max.
	 * 
	 * A demo method including a while loop.
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
		while ( i < values.length) {
			
			int j = values[i++];
			if (j > max) {
				max = j;
			}
		}
		return max;
	}

	/**
	 * Middle.
	 * 
	 * Another simple demo method.
	 * Returns the middle Value of a given array.
	 * For demo purpose.
	 * 
	 * @param myArray
	 *            the integer array
	 * 
	 * @return the integer in the middle of the array.
	 * 
	 */
	/*@ public normal_behavior ensures true; @*/
	public int middle(int[] myArray) {
		
		int i = myArray.length / 2;
		return myArray[i];
	}
}
/**
  
 Here the Debug.sep(); statements are inserted.
 
package tests;

public class HowTacletsWork {

	Debug.sep(0);
	/*@ public normal_behavior ensures true; @
	public int max(int[] values) {
	Debug.sep(1);
		int max = values[Debug.sep(8,0)];
		Debug.sep(2);
		int i = 0;
		Debug.sep(3);
		while (Debug.sep(9, i < values.length) ) {
			Debug.sep(4);
			int j = values[Debug.sep(10,i++)];
			Debug.sep(5);
			if (Debug.sep(11,j > max)) {
			Debug.sep(6);
				max = j;
			}
		}Debug.sep(7);
		return max;
	}

	/*@ public normal_behavior ensures true; @
	public int middle(int[] myArray) {
		Debug.sep(12);
		int i = myArray.length / 2;
		Debug.sep(13);
		return myArray[Debug.sep(14,i)];
	}
}
*/
