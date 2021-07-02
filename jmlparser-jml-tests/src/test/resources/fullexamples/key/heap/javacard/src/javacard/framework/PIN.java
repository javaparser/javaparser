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

public interface PIN {

    //@ public instance model \locset validatedRep;
    //@ public instance model boolean isValidated;

    //@ public accessible isValidated : footprint;
    //@ public accessible validatedRep : footprint;

    //@ public instance model \locset triesRep;
    //@ public instance model byte triesLeft;

    //@ public accessible triesLeft : footprint;
    //@ public accessible triesRep : footprint;

    //@ public instance model \locset footprint;
    //@ public accessible \inv : footprint;
    //@ public accessible footprint : footprint;

    //@ public instance model byte maxTries;
    //@ public accessible maxTries : footprint;
    //@ public instance invariant maxTries > 0 && maxTries <= 127;

    //@ public instance model byte maxPINSize;
    //@ public accessible maxPINSize : footprint;
    //@ public instance invariant maxPINSize > 0 && maxPINSize <= 127;

    //@ public instance invariant triesLeft >= 0 && triesLeft <= maxTries;
 
    /*@ public normal_behavior
          requires true;
          ensures \result == isValidated;
          accessible footprint;
      @*/
    public /*@ strictly_pure @*/ boolean isValidated();

    /*@ public normal_behavior
          requires true;
          ensures \result == triesLeft;
          accessible footprint;
       @*/
    public /*@ strictly_pure @*/ byte getTriesRemaining();

    /*@ public normal_behavior
          requires javacard.framework.JCSystem.getTransactionDepth() == 0;
          ensures \old(isValidated) ==> (!isValidated && triesLeft == maxTries);
          ensures !\old(isValidated) ==> (isValidated == \old(isValidated) && triesLeft == \old(triesLeft));
          ensures \new_elems_fresh(triesRep) && \new_elems_fresh(validatedRep);
          assignable triesRep, validatedRep;
      @*/
    public void reset();

    /*@ public behavior
          requires<savedHeap> javacard.framework.JCSystem.getTransactionDepth() == 1;
          requires JCSystem.npe != null;
          requires JCSystem.aioobe != null;
          ensures \result <==> isValidated;
          ensures \old(triesLeft) == 0 ==> (triesLeft == 0 && !isValidated);
          ensures length != maxPINSize ==> !isValidated;
          ensures isValidated ==> triesLeft == maxTries;
          ensures (!isValidated && \old(triesLeft) > 0) ==> triesLeft == \old(triesLeft) - 1;
          ensures \new_elems_fresh(triesRep) && \new_elems_fresh(validatedRep);
          ensures<savedHeap> \new_elems_fresh(\backup(triesRep)) && \new_elems_fresh(\backup(validatedRep));
          signals (NullPointerException e) pin == null && !isValidated && triesLeft == \old(triesLeft) - 1;
          signals (ArrayIndexOutOfBoundsException e) (length < 0 || length > maxPINSize || offset < 0 || offset + length > pin.length)
                            && !isValidated && triesLeft == \old(triesLeft) - 1;
          signals_only NullPointerException, ArrayIndexOutOfBoundsException;
          assignable<heap><savedHeap> triesRep, validatedRep;
      @*/
    public boolean check(/*@ nullable @*/ byte[] pin, short offset, byte length)
            throws NullPointerException, ArrayIndexOutOfBoundsException;

}
