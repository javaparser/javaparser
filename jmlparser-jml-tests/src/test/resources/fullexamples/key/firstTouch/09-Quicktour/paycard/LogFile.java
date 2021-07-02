package paycard;

public class LogFile {
    /*@ public invariant logArray != null 
      @                  && \nonnullelements(logArray)
      @                  && logArray.length == logFileSize 
      @                  && currentRecord < logFileSize
      @                  && currentRecord >= 0
      @                  && LogRecord.transactionCounter >= 0;
      @   accessible \inv: this.*, this.logArray[*], 
      @    LogRecord.transactionCounter, logFileSize;
      @*/   
    private /*@ spec_public @*/ final static int logFileSize = 3;
    private /*@ spec_public @*/ int currentRecord;
    private /*@ spec_public @*/ LogRecord[] logArray = new LogRecord[logFileSize];

    

    
    /*@ public normal_behavior
      @ requires LogRecord.transactionCounter >= 0;
      @ ensures (\forall int x; 0 <= x && x < logArray.length; \fresh(logArray[x]));
      @ ensures currentRecord == 0  && LogRecord.transactionCounter >= 0;
      @ assignable LogRecord.transactionCounter;
      @*/
    public /*@pure@*/ LogFile() {
	int i=0;
        /*@ loop_invariant
          @ 0 <= i && i <= logArray.length &&
          @ (\forall int x; 0 <= x && x < i; logArray[x] != null && 
          @ \fresh(logArray[x])) && LogRecord.transactionCounter >= 0;
          @ assignable logArray[*], LogRecord.transactionCounter;
          @ decreases logArray.length - i; 
          @*/
	while(i<logArray.length){
	    logArray[i++] = new LogRecord();
	}
	currentRecord = 0;
    }
    
    /*@ public normal_behavior 
      @    requires balance >= 0;
      @    requires LogRecord.transactionCounter >= 0;    
      @    ensures \old(currentRecord) + 1 != logFileSize 
      @            ? currentRecord == \old(currentRecord) + 1 
      @            : currentRecord == 0;
      @    ensures logArray[currentRecord].balance == balance;
      @    ensures LogRecord.transactionCounter >= 0;
      @    assignable currentRecord, 
      @               logArray[currentRecord == logFileSize-1 ? 0 : currentRecord + 1].*,
      @               LogRecord.transactionCounter;
      @*/
    public void addRecord(int balance) throws CardException {
	currentRecord++;
	if (currentRecord == logFileSize) currentRecord = 0;
	logArray[currentRecord].setRecord(balance);
    }
    
    
    /*@ public normal_behavior
      @    requires (\forall int i; 0 <= i && i<logArray.length;
      @             logArray[i].\inv);
      @    ensures (\forall int i; 0 <= i && i<logArray.length;
      @             logArray[i].balance <= \result.balance);
      @    diverges true;
      @ */
    public /*@pure@*/ LogRecord getMaximumRecord(){
	LogRecord max = logArray[0];
	int i=1;
	/*@ loop_invariant
	  @   0<=i && i <= logArray.length 
	  @   && max!=null &&
	  @   (\forall int j; 0 <= j && j<i; 
	  @     max.balance >= logArray[j].balance);
	  @ assignable \nothing;
	  @ decreases logArray.length - i; 
	  @*/
	while(i<logArray.length){
	    LogRecord lr = logArray[i++];
	    if (lr.getBalance() > max.getBalance()){
		max = lr;
	    }
	}
	return max;
    }
}
