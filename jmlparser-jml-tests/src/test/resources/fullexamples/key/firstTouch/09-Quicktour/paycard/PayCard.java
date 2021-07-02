package paycard;

public class PayCard {
    /*@ public invariant log.\inv; 
      @ public invariant balance >= 0; 
      @ public invariant limit > 0;
      @ public invariant unsuccessfulOperations >= 0; 
      @ public invariant log != null;
      @*/
   
   /*@ spec_public @*/  int limit=1000;
    /*@ spec_public @*/ int unsuccessfulOperations;
    /*@ spec_public @*/ int id;
    /*@ spec_public @*/ int balance=0;
    /*@ spec_public @*/ protected LogFile log;
    
  /*@ public normal_behavior
    @  requires limit > 0;
    @  requires LogRecord.transactionCounter >= 0;
    @  ensures LogRecord.transactionCounter >= 0;
    @  ensures this.balance == 0 && this.unsuccessfulOperations == 0 && 
    @     log != null && this.limit== limit;
    @  assignable this.limit, this.unsuccessfulOperations, this.balance, 
    @     this.log, LogRecord.transactionCounter;
    @*/
     
    public PayCard(int limit) {
	balance = 0;
	unsuccessfulOperations=0;
	this.limit=limit;
	this.log = new LogFile();
    }
    
  /*@ public normal_behavior
    @ 
    @   requires LogRecord.transactionCounter >= 0;
    @   ensures LogRecord.transactionCounter >= 0;
    @   ensures this.balance == 0 && this.unsuccessfulOperations == 0 && log != null;
    @   assignable this.unsuccessfulOperations, this.balance, this.log,
    @   LogRecord.transactionCounter;
    @*/
    public PayCard() {
	balance=0;
	unsuccessfulOperations=0;
	this.log = new LogFile();
    }
    

     /*@ public normal_behavior
      @ requires LogRecord.transactionCounter >= 0;
      @ ensures \result.limit==100;
      @ ensures LogRecord.transactionCounter >= 0;
      @  ensures \result.balance == 0 && \result.unsuccessfulOperations == 0 && 
      @     \result.log != null && \fresh(\result);
      @*/
    public static PayCard createJuniorCard() {
	return new PayCard(100);
    }
    


    /*@
      @ public normal_behavior
      @     requires amount>0;
      @     requires amount + balance < limit && isValid() == true;
      @     ensures \result == true && amount == \old(amount);
      @     ensures balance == amount + \old(balance);
      @     ensures unsuccessfulOperations == \old(unsuccessfulOperations);
      @     assignable balance, unsuccessfulOperations;
      @
      @     also
      @
      @ public normal_behavior
      @     requires amount>0 ;
      @     requires amount + balance >= limit || isValid() == false;
      @     ensures \result == false && amount == \old(amount);
      @     ensures unsuccessfulOperations == \old(unsuccessfulOperations) + 1; 
      @     ensures balance == \old(balance);
      @     assignable balance, unsuccessfulOperations;
      @ 	
      @ also
      @
      @ public exceptional_behavior
      @     requires amount <= 0;
      @     assignable \nothing;
      @*/  
    public boolean charge(int amount) throws IllegalArgumentException {
	if (amount <= 0) {
	    throw new IllegalArgumentException();
	}
	if (this.balance+amount<this.limit && this.isValid()) {
	    this.balance=this.balance+amount;
	    return true;
	} else {
	    this.unsuccessfulOperations++;
	    return false;
	}
    }
    
   /*@
     @ public normal_behavior
     @ requires amount>0 && log.\inv;
     @ requires log != null && this != null;
     @ requires LogRecord.transactionCounter >= 0;
     @ ensures balance >= \old(balance);  
     @*/
     
    public void chargeAndRecord(int amount) {
	if (charge(amount)) {
	    try {
		log.addRecord(balance);
	    } catch (CardException e){
		throw new IllegalArgumentException();
	    }
	}
    }
    
    /*@
      @ public normal_behavior
      @ requires true;
      @ ensures \result == (unsuccessfulOperations<=3); 
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ boolean isValid() {
	if (unsuccessfulOperations<=3) {
	    return true;
	} else {
	    return false;
	}
    }
    
    public String infoCardMsg() {
	return (" Current balance on card is " + balance);
    }
}
