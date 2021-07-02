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

public class TransactionException extends CardRuntimeException {

    private static /*@ spec_public nullable @*/ TransactionException _systemInstance = new TransactionException();

    public final static short IN_PROGRESS = (short) 1;
    // @ public static invariant IN_PROGRESS == 1;
    public final static short NOT_IN_PROGRESS = (short) 2;
    // @ public static invariant NOT_IN_PROGRESS == 2;
    public final static short BUFFER_FULL = (short) 3;
    // @ public static invariant BUFFER_FULL == 3;
    public final static short INTERNAL_FAILURE = (short) 4;
    // @ public static invariant INTERNAL_FAILURE == 4;

    /*@ public exceptional_behavior
      @   requires TransactionException._systemInstance != null;
      @   requires TransactionException._systemInstance.\inv;
      @   requires \typeof(TransactionException._systemInstance) == \type(TransactionException);
      @   assignable TransactionException._systemInstance.footprint;
      @   signals (TransactionException te)
             te == TransactionException._systemInstance
          && ((TransactionException)te).reason == reason
          && \new_elems_fresh(TransactionException._systemInstance.footprint);
      @   signals_only TransactionException;
      @*/
    public static void throwIt(short reason) throws TransactionException {
        TransactionException._systemInstance.setReason(reason);
        throw TransactionException._systemInstance;
    }

}
