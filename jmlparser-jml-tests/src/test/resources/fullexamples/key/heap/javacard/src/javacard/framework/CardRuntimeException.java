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

public class CardRuntimeException extends java.lang.RuntimeException {

    private static /*@ spec_public nullable @*/ CardRuntimeException _systemInstance = new CardRuntimeException();

    //@ public model instance \locset footprint;
    //@ public model instance short reason;
    //@ public accessible \inv : footprint;
    //@ public accessible footprint : footprint;
    //@ public accessible reason : footprint;

    protected /*@ spec_public non_null @*/ short[] _reason;
    //@ public instance invariant _reason.length == 1;
    //@ public instance invariant JCSystem.isTransient(_reason) == JCSystem.CLEAR_ON_RESET; 

    //@ public represents reason = _reason[0];
    //@ public represents footprint = _reason, _reason[0], _reason.\transient;

    /*@ public normal_behavior
      @   ensures \fresh(footprint);
      @   ensures this.reason == reason;
      @   assignable \nothing;
      @*/
    public CardRuntimeException(short reason) {
       this();
       setReason(reason);
    }

    /*@ public normal_behavior
      @   ensures \fresh(footprint);
      @   ensures this.reason == 0;
      @   assignable \nothing;
      @*/
    CardRuntimeException() {
        short one = (short)1;
        _reason = JCSystem.makeTransientShortArray(one, JCSystem.CLEAR_ON_RESET);
    }

    /*@ public normal_behavior
      @   ensures \result == reason;
      @   accessible footprint;
      @*/
    public /*@ strictly_pure @*/ short getReason() {
        return _reason[0];
    }

    /*@ public normal_behavior
      @   ensures this.reason == reason;
      @   ensures \new_elems_fresh(footprint);
      @   assignable footprint;
      @*/
    public void setReason(short reason) {
        _reason[0] = reason;
    }

    /*@ public exceptional_behavior
      @   requires \typeof(CardRuntimeException._systemInstance) == \type(CardRuntimeException);
      @   requires CardRuntimeException._systemInstance != null;
      @   requires CardRuntimeException._systemInstance.\inv;
      @   assignable CardRuntimeException._systemInstance.footprint;
      @   signals (CardRuntimeException cre)
             cre == CardRuntimeException._systemInstance
          && ((CardRuntimeException)cre).reason == reason
          && \new_elems_fresh(CardRuntimeException._systemInstance.footprint);
      @   signals_only CardRuntimeException;
      @*/
    public static void throwIt(short reason) throws CardRuntimeException {
        CardRuntimeException._systemInstance.setReason(reason);
        throw CardRuntimeException._systemInstance;
    }

}
