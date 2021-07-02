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

class Break {

    public static void tryBreak(int i){
       	l1:{
	    try{
		if (i==0) break l1;
	}
	    catch (Exception e){}
	    finally{ 
		i=i+1;
	    }
	}
	i=i+1;
	return i;
    }

}
