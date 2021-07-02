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

import javacard.framework.*;


public class Examples {

  short balance = 0; //@ public invariant balance >= 0;
  short operationCount = 0; //@ public invariant operationCount >= 0;

  /*@ public normal_behavior
        requires JCSystem.getTransactionDepth() == 0;
        requires this.balance + change >= 0;
        ensures this.balance == \old(this.balance) + change;
        ensures this.operationCount == \old(this.operationCount) + 1;
        ensures \result == \old(this.balance) + change;
      also 
      public normal_behavior
        requires JCSystem.getTransactionDepth() == 0;
        requires this.balance + change < 0;
        ensures this.balance == \old(this.balance);
        ensures this.operationCount == \old(this.operationCount);
        ensures \result == \old(this.balance) + change;
    @*/
  public short updateBalance(short change) {
    short newBalance = 0;
    JCSystem.beginTransaction();
    this.operationCount++;
    newBalance = (short)(this.balance + change);
    if(newBalance < 0) {
      JCSystem.abortTransaction();
      return newBalance;
    }
    this.balance = newBalance;
    JCSystem.commitTransaction();
    return newBalance;
  }

  /*@ public normal_behavior
        requires JCSystem.npe != null && JCSystem.aioobe != null;
        requires a != null && a.length > 0;
        requires !\transactionUpdated(a);

        requires JCSystem.getTransactionDepth() == 0;   
        requires JCSystem.isTransient(a) == JCSystem.NOT_A_TRANSIENT_OBJECT;

        ensures a[0] == 1;
    @*/
  public void setArray1(byte[] a) {
    short zero = (short)0; short one = (short)1; byte bone = (byte)1;
    JCSystem.beginTransaction();
      Util.arrayFillNonAtomic(a, zero, one, bone); // NA a[0] = 1;
      a[0] = 2;
    JCSystem.abortTransaction();
  }

  /*@ public normal_behavior
        requires JCSystem.npe != null && JCSystem.aioobe != null;
        requires a != null && a.length > 0;
        requires !\transactionUpdated(a);

        requires JCSystem.getTransactionDepth() == 0;   
        requires JCSystem.isTransient(a) == JCSystem.NOT_A_TRANSIENT_OBJECT;

        ensures a[0] == \old(a[0]);
    @*/
  public void setArray2(byte[] a) {
    short zero = (short)0; short one = (short)1; byte bone = (byte)1;
    JCSystem.beginTransaction();
      a[0] = 2;
      Util.arrayFillNonAtomic(a, zero, one, bone); // NA a[0] = 1;
    JCSystem.abortTransaction();
  }

}
