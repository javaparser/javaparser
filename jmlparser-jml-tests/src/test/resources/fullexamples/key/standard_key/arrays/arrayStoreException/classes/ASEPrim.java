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

public class ASEPrim {
    int[][] g;

  /*@ normal_behavior
    @  ensures true;
    @*/
  public static void main(String[] args) {
    Object[] o = new Object[3];
    o[0] = new byte[3][2];
    ((Object[])(o[0]))[0] = (Object)new int[2];
  }
}
                     
