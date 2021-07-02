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

public class KiAdClass extends AdClass {
    private int a = 1;
    private int d = 4;
    protected int e = 5;
}

class AdClass {
    private int a = 0;
    protected int b = 0;
    public int c = 0;

    private AdClass next;
    private AdClass left;
    private AdClass right;
}
