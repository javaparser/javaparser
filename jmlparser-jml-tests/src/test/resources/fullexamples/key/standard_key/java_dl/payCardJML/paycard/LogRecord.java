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

    private /*@ spec_public @*/ static int transactionCounter = 0;

    private /*@ spec_public @*/ int balance = -1;
    private /*@ spec_public @*/ int transactionId = -1;
    private /*@ spec_public @*/ boolean empty = true;
    
    /*@ public invariant
      @     !empty ==> (balance >= 0 && transactionId >= 0);
      @*/
    

    public /*@pure@*/ LogRecord() {}


    /*@ public normal_behavior
      @   requires balance >= 0 && transactionCounter >= 0;
      @   assignable empty, this.balance, transactionId, transactionCounter;
      @   ensures this.balance == balance 
      @           && transactionId == \old(transactionCounter);
      @   ensures \inv && transactionCounter >= 0;
      @*/
    public /*@helper@*/ void setRecord(int balance) throws CardException {
	if(balance < 0) {
	    throw new CardException();
	}
    	this.empty = false;
    	this.balance = balance;
        this.transactionId = transactionCounter++;
    }

    
    /*@ public normal_behavior
      @   ensures \result == balance;
      @*/
    public /*@pure helper@*/ int getBalance() {
	return balance;
    }

    
    /*@ public normal_behavior
      @   ensures \result == transactionId;
      @*/
    public /*@pure helper@*/ int getTransactionId() {
	return transactionId;
    }
}
