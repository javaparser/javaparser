package paycard;

public class LogRecord {
    
    /*@ public invariant
      @     !empty ==> (balance >= 0 && transactionId >= 0);
      @ accessible \inv: this.empty, this.balance, transactionCounter, this.transactionId;
      @*/
    
    private /*@ spec_public @*/ static int transactionCounter = 0;
    
    private /*@ spec_public @*/ int balance = -1;
    private /*@ spec_public @*/ int transactionId = -1;
    private /*@ spec_public @*/ boolean empty = true;
    
    

    public /*@pure@*/ LogRecord() {
    }
    
      
    /*@ public normal_behavior
      @   requires balance >= 0 && transactionCounter >= 0;
      @   ensures this.balance == balance 
      @           && transactionId == \old(transactionCounter);
      @   ensures \inv && transactionCounter >= 0;
      @   assignable empty, this.balance, transactionId, transactionCounter;
      @*/
    public /*@helper@*/ void setRecord(int balance) throws CardException {
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
    public /*@helper strictly_pure@*/ int getBalance() {
	return balance;
    }
    
    /*@ public normal_behavior
      @   ensures \result == transactionId;
      @*/
    public /*@pure helper@*/ int getTransactionId() {
	return transactionId;
    }
}
