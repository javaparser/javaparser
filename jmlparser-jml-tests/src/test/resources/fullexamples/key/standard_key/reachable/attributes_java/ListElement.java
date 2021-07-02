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

public class ListElement {

    public ListElement oldNext;

    private ListElement next;

    private ListElement help;


    public ListElement reverse() {
	ListElement p = null;
	ListElement c = this; 
	ListElement tmp = null;
	while(c!=null) {
	    tmp = c;
	    c = c.next;
	    tmp.next = p;
	    p = tmp;
	}
	return p;
    }


    public ListElement getLast() {
	help = this; 
	while(help.next!=null) {
	    help = help.next;
	}
	return help;
    }
}
