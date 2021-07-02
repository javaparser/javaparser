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

public class OwnerPIN implements PIN {

    private byte _maxPINSize;  //@ public represents maxPINSize = _maxPINSize;
    private byte _maxTries;    //@ public represents maxTries = _maxTries;

    private /*@ spec_public non_null @*/ boolean[] _isValidated;
    /*@ public invariant
            _isValidated.length == 1
          && JCSystem.isTransient(_isValidated) == JCSystem.CLEAR_ON_RESET
          && !\transactionUpdated(_isValidated); @*/

    //@ public represents validatedRep = \locset(_isValidated[0]);
    //@ public represents isValidated = _isValidated[0];

    private /*@ spec_public non_null @*/ byte[] _pin;
    /*@ public invariant _pin.length == maxPINSize + 1 &&
                         JCSystem.isTransient(_pin) == JCSystem.NOT_A_TRANSIENT_OBJECT &&
                         !\transactionUpdated(_pin); @*/
    //@ public represents triesRep = _pin[0], _pin.\transient, \transactionUpdated(_pin);
    //@ public represents triesLeft = _pin[0];


    /*@ public represents footprint = 
           this.*,
           _pin[*], _pin.\transient, \transactionUpdated(_pin), 
           _isValidated[*], _isValidated.\transient, \transactionUpdated(_isValidated);
      @*/

    /*@ public normal_behavior
          requires true;
          ensures \result == isValidated;
          accessible footprint;
      @*/
    protected /*@ strictly_pure @*/ boolean getValidatedFlag() {
        return _isValidated[0];
    }

    /*@ public normal_behavior
          requires<savedHeap> javacard.framework.JCSystem.getTransactionDepth() == 1;
          ensures isValidated == value;
          assignable<heap><savedHeap> validatedRep;
    @*/
    protected void setValidatedFlag(boolean value) {
        _isValidated[0] = value;
    }

    /*@ public normal_behavior 
          requires javacard.framework.JCSystem.getTransactionDepth() == 0;
          requires maxTries > 0 && maxTries <= 127;
          requires maxPINSize > 0 && maxPINSize <= 127;
          ensures \fresh(footprint) && \fresh(validatedRep) && \fresh(triesRep);
          ensures this.maxPINSize == maxPINSize;
          ensures this.maxTries == maxTries;
          ensures triesLeft == maxTries;
          ensures !isValidated;
          assignable \nothing;
    @*/
    public OwnerPIN(byte maxTries, byte maxPINSize) throws PINException {
        if (maxPINSize < 1) {
            PINException.throwIt(PINException.ILLEGAL_VALUE);
        }
        _pin = new byte[maxPINSize + 1];
        short one = (short)1;
        _isValidated = JCSystem.makeTransientBooleanArray(one,
                JCSystem.CLEAR_ON_RESET);
        _pin[0] = maxTries;
        _maxTries = maxTries;
        _maxPINSize = maxPINSize;
        _isValidated[0] = false;
    }


    /*@ public exceptional_behavior
          requires \disjoint(footprint, PINException._systemInstance.footprint);
          requires javacard.framework.JCSystem.getTransactionDepth() == 0;
          requires JCSystem.npe != null;
          requires JCSystem.aioobe != null;
          requires PINException._systemInstance != null;
          requires \typeof(PINException._systemInstance) == \type(PINException);
          requires PINException._systemInstance.\inv;
          requires length > maxPINSize; 
          signals (PINException pe) true
            && ((PINException)pe).reason == PINException.ILLEGAL_VALUE
            && \new_elems_fresh(PINException._systemInstance.footprint);
          signals_only PINException;
          assignable PINException._systemInstance.footprint;
        
        also

        public behavior
          requires \disjoint(footprint, PINException._systemInstance.footprint);
          requires javacard.framework.JCSystem.getTransactionDepth() == 0;
          requires JCSystem.npe != null;
          requires JCSystem.aioobe != null;
          requires PINException._systemInstance != null;
          requires \typeof(PINException._systemInstance) == \type(PINException);
          requires PINException._systemInstance.\inv;
          requires length <= maxPINSize; 
          ensures triesLeft == maxTries;
          ensures !isValidated;
          // ensures (\forall short i; i>=0 && i < length; _pin[1 + i] == \old(pin[offset + i]));
          ensures \new_elems_fresh(footprint);
          signals (NullPointerException npe) npe == JCSystem.npe && pin == null;
          signals (ArrayIndexOutOfBoundsException aioobe)
             aioobe == JCSystem.aioobe && (length < 0 || offset < 0 || offset + length > pin.length);
          signals_only NullPointerException, ArrayIndexOutOfBoundsException;
          assignable footprint;
      @*/
    public void update(/*@ nullable @*/ byte[] pin, short offset, byte length)
            throws PINException, ArrayIndexOutOfBoundsException, NullPointerException {
        if (length > _maxPINSize) {
            PINException.throwIt(PINException.ILLEGAL_VALUE);
        }
        short one = (short)1;
        Util.arrayCopy(pin, offset, _pin, one, length);
        _pin[0] = _maxTries;
        setValidatedFlag(false);
    }

    /*@ public normal_behavior
          requires javacard.framework.JCSystem.getTransactionDepth() == 0;
          ensures !isValidated && triesLeft == maxTries;
          ensures \new_elems_fresh(triesRep) && \new_elems_fresh(validatedRep);
          assignable triesRep, validatedRep;
      @*/
    public void resetAndUnblock() {
        setValidatedFlag(false);
        _pin[0] = _maxTries;
    }

    // Specified in PIN.java
    public boolean check(/*@ nullable @*/ byte[] pin, short offset, byte length)
            throws NullPointerException, ArrayIndexOutOfBoundsException {
        setValidatedFlag(false);
        if (getTriesRemaining() == 0)
            return false;
        short zero = (short)0;
        short one = (short)1;
        byte tmp = (byte) (_pin[0] - 1);
        Util.arrayFillNonAtomic(_pin, zero, one, tmp);
        if (length != _maxPINSize)
            return false;
        if (Util.arrayCompare(_pin, one, pin, offset, length) == 0) {
            setValidatedFlag(true);
            _pin[0] = _maxTries;
            return true;
        }
        return false;
    }

    // Specified in PIN.java
    public void reset() {
        if (isValidated())
            resetAndUnblock();
    }

    // Specified in PIN.java
    public boolean isValidated() {
        return getValidatedFlag();
    }

    // Specified in PIN.java
    public byte getTriesRemaining() {
        return _pin[0];
    }

}
