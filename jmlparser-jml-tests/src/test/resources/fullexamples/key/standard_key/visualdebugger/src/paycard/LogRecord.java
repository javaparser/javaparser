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

package paycard;

public class LogRecord {

    /*@ public instance invariant
      @     !empty ==> (balance >= 0 && transactionId >= 0);
      @ public static invariant transactionCounter >= 0;
      @*/
    
    private /*@ spec_public @*/ static int transactionCounter = 0;

    private /*@ spec_public @*/ int balance = -1;
    private /*@ spec_public @*/ int transactionId = -1;
    private /*@ spec_public @*/ boolean empty = true;

    public /*@pure@*/ LogRecord() {}


    /*@ public normal_behavior
      @   requires balance >= 0;
      @   assignable empty, this.balance, transactionId, transactionCounter;
      @   ensures this.balance == balance && 
      @           transactionId == \old(transactionCounter);
      @*/
    public void setRecord(int balance) throws CardException {
	if(balance < 0){
	    throw new CardException();
	}
    	this.empty = false;
    	this.balance = balance;
        this.transactionId = transactionCounter++;
    }

    /*@ public normal_behavior
      @   ensures \result == balance;
      @*/
    public /*@pure@*/ int getBalance() {
	return balance;
    }

    /*@ public normal_behavior
      @   ensures \result == transactionId;
      @*/
    public /*@pure@*/ int getTransactionId() {
	return transactionId;
    }
}
