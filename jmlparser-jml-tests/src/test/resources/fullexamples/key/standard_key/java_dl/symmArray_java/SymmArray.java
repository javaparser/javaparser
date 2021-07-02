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

public class SymmArray {

    public int[][] ar;

    /*@ public invariant
      @   ar != null &&
      @   (\forall int i; i >= 0 && i < ar.length;
      @                   ar[i] != null && ar[i].length == ar.length) &&
      @   (\forall int i, j; i >= 0 && i < ar.length && j >= 0 && j < ar.length && i != j;
      @                      ar[i] != ar[j]);
      @*/

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result ==
      @     (\forall int i, j; i >= 0 && i < ar.length && j >= 0 && j < ar.length;
      @                        ar[i][j] == ar[j][i]);
      @*/
    public boolean IsSymmetric() {}

    /*@ public normal_behavior
      @   requires
      @     ar.length >= 10 &&
      @     (\forall int i, j; i >= 0 && i < ar.length && j >= 0 && j < ar.length;
      @                        ar[i][j] == ar[j][i]);
      @   ensures
      @     (\forall int i, j; i >= 0 && i < ar.length && j >= 0 && j < ar.length;
      @                        ar[i][j] == ar[j][i]);
      @*/
    public void assignA() {
	ar[0][0] = 0;
	ar[1][1] = 1;
	ar[2][2] = 2;
	ar[3][3] = 3;
	ar[4][4] = 4;
	ar[5][5] = 5;
	ar[6][6] = 6;
	ar[7][7] = 7;
	ar[8][8] = 8;
	ar[9][9] = 9;
    }

    /*@ public normal_behavior
      @   requires ar.length >= 10 && IsSymmetric();
      @   ensures IsSymmetric();
      @*/
    public void assignB() {
	ar[0][0] = 0;
	ar[1][1] = 1;
	ar[2][2] = 2;
	ar[3][3] = 3;
	ar[4][4] = 4;
	ar[5][5] = 5;
	ar[6][6] = 6;
	ar[7][7] = 7;
	ar[8][8] = 8;
	ar[9][9] = 9;
    }
}
