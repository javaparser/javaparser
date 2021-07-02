// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package javacard.framework;

public class PINException extends CardRuntimeException {

    private static /*@ spec_public nullable @*/ PINException _systemInstance = new PINException();
    // @ public static invariant PINException._systemInstance != null;

    public static final short ILLEGAL_VALUE = (short) 1;
    // @ public static invariant ILLEGAL_VALUE == 1;

    /*@ public exceptional_behavior
      @   requires PINException._systemInstance != null;
      @   requires PINException._systemInstance.\inv;
      @   requires \typeof(PINException._systemInstance) == \type(PINException);
      @   assignable PINException._systemInstance.footprint;
      @   signals (PINException pe)
             pe == PINException._systemInstance
          && ((PINException)pe).reason == reason
          && \new_elems_fresh(PINException._systemInstance.footprint);
      @   signals_only PINException;
      @*/
    public static void throwIt(short reason) throws PINException {
        PINException._systemInstance.setReason(reason);
        throw PINException._systemInstance;
    }

}
