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

public class ContinueLabel {

    public static void main(String args[]) {
	System.out.println(test2());
    }

    static int test() {
	
	int x=1,y=1,z=0;
	lll:while (x>0) {
	    z++;
	    try {
		b:l4:while (y>0)
		    {
			y--;
			z++;
			if (y==0) continue lll; 
			continue b;
		    }
	    } catch (Exception e){}
	    finally{z++;}
	    x--;
	    z++;
	}
	
	return z;
    }

    static int test1() {
	
	int x=1,y=1,z=0;
	lll:while (x>0) {
	    z++;

	    x--;
	    z++;
	    continue;
	}
	
	return z;
    }

    static int test2() {
	int x=1,y=1,z=0;
	l1:while (x>0) {
	    z++;
	    try {
	  	l2:while (y>0)
		    {
			y--;
			try{
			    l3:while (x==1) {
				continue l1;
			    }
			} catch (Exception e){}
			finally {z++;}
		    }
	    } catch (Exception e){}
	    finally{z++;}
	    x--;
	    z++;
	}
	
	return z;
    
    }

}
