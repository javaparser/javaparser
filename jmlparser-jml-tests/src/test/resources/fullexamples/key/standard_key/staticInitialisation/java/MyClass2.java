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

public class MyClass2 {

    public static Object[] o;
    public static MyClass2 my;
    public static MyClass2[][] mine;


    public static void main(String[] args) {
	     MyClass2 d = null;
	     MyClass2.mine[0][0].my = d;
	     System.out.println(MyClass2.my);
    }

}
