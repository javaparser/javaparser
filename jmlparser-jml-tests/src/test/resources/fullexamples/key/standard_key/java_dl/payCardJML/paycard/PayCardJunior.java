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


public class PayCardJunior extends PayCard {
    
    /*@ spec_public @*/ private final static int juniorLimit = 100;    

    /*@ public invariant balance < juniorLimit 
      @                  && juniorLimit < limit; 
      @*/

    /*@ public represents value = balance;
      @ public represents regularState = (unsuccessfulOperations <= 3);
      @*/    
    
    
    /*@ public normal_behavior
      @   requires LogRecord.transactionCounter >= 0;
      @   requires cardLimit > juniorLimit;
      @   assignable LogRecord.transactionCounter;
      @   ensures this.limit == cardLimit;
      @   ensures  LogRecord.transactionCounter >= 0;
      @*/
    public PayCardJunior(int cardLimit) {
	super(cardLimit);
    }

    
    /*@ public normal_behavior
      @   requires LogRecord.transactionCounter >= 0; 
      @   assignable LogRecord.transactionCounter;
      @   ensures \result.limit == 1000;
      @   ensures  LogRecord.transactionCounter >= 0;      
      @*/
    public static PayCardJunior createCard() {
	return new PayCardJunior(1000);
    }

    
    /*@ also public normal_behavior
      @   requires amount > 0;
      @   ensures \old(balance) + amount < juniorLimit
      @           ? balance == \old(balance) + amount
      @           : (balance == \old(balance) 
      @              && unsuccessfulOperations == \old(unsuccessfulOperations) + 1);
      @*/
    public void charge(int amount) {
        try {
            charge0(amount);
        } catch (java.lang.Exception e) {
            this.unsuccessfulOperations++;
        }
    }
    

    /*@ private exceptional_behavior
      @   requires amount <= 0 || checkSum(this.balance + amount) == 0;
      @   assignable \nothing;
      @   signals_only CardException;
      @   signals (CardException ce) ce != null && (amount <= 0 || checkSum(this.balance + amount) == 0);
      @ also private normal_behavior
      @   requires amount > 0 && checkSum(this.balance + amount) == 1;
      @   ensures balance == \old(balance) + amount;
      @*/
    private void charge0(int amount) throws CardException {
	if(amount <= 0){
	    throw new CardException();
	} 
        int checkStatus = this.checkSum(this.balance + amount);
        if(checkStatus != 1) {
            throw new CardException();
        } else {
            this.balance = this.balance + amount;
	    log.addRecord(balance);
        }
    }
    
    
    /*@ private normal_behavior
      @   ensures \result == 1 ?  sum < juniorLimit : sum >= juniorLimit;
      @   ensures \result == 1 || \result == 0;
      @*/
    private /*@pure@*/ int checkSum(int sum) {
        if(sum >= this.juniorLimit) {
            return 0;
        } else {
            return 1;
        }
    }

    
    /*@ public normal_behavior
      @   requires amount>0;
      @   ensures \old(balance) + amount < juniorLimit 
      @           ? amount == balance - \old(balance) 
      @           : (balance == \old(balance) 
      @              && unsuccessfulOperations == \old(unsuccessfulOperations) + 1);
      @*/
    public void complexCharge(int amount) {
        try {
            this.charge0(amount);
        } catch (CardException e) {
            this.unsuccessfulOperations++;
        }
    }
}
