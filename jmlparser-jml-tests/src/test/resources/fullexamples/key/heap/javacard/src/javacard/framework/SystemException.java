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

public class SystemException extends CardRuntimeException {

    private static /*@ spec_public nullable @*/ SystemException _systemInstance = new SystemException();
    // @ public invariant SystemException._systemInstance != null;

    public static final short ILLEGAL_VALUE = (short) 1;
    // @ public static invariant ILLEGAL_VALUE == 1;
    public static final short NO_TRANSIENT_SPACE = (short) 2;
    // @ public static invariant NO_TRANSIENT_SPACE == 2;
    public static final short ILLEGAL_TRANSIENT = (short) 3;
    // @ public static invariant ILLEGAL_TRANSIENT == 3;
    public static final short ILLEGAL_AID = (short) 4;
    // @ public static invariant ILLEGAL_AID == 4;
    public static final short NO_RESOURCE = (short) 5;
    // @ public static invariant NO_RESOURCE == 5;
    public static final short ILLEGAL_USE = (short) 6;
    // @ public static invariant ILLEGAL_USE == 6;

    /*@ public exceptional_behavior
      @   requires SystemException._systemInstance != null;
      @   requires SystemException._systemInstance.\inv;
      @   requires \typeof(SystemException._systemInstance) == \type(SystemException);
      @   assignable SystemException._systemInstance.footprint;
      @   signals (SystemException se)
             se == SystemException._systemInstance
          && ((SystemException)se).reason == reason
          && \new_elems_fresh(SystemException._systemInstance.footprint);
      @   signals_only SystemException;
      @*/
    public static void throwIt(short reason) throws SystemException {
        SystemException._systemInstance.setReason(reason);
        throw SystemException._systemInstance;
    }
}
