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


public class LogFile {    
    
    private /*@ spec_public @*/ static final int logFileSize = 3;
    private /*@ spec_public @*/ int currentRecord;
    private /*@ spec_public nullable@*/ LogRecord[] logArray = new LogRecord[logFileSize];
    

    /*@ public invariant logArray != null 
      @                  && \nonnullelements(logArray)
      @                  && logArray.length == logFileSize 
      @                  && currentRecord < logFileSize
      @                  && currentRecord >= 0
      @                  && LogRecord.transactionCounter >= 0;
      @*/
    
    //@ public accessible \inv: this.*, this.logArray[*], LogRecord.transactionCounter;

    
    /*@ public normal_behavior
      @   requires LogRecord.transactionCounter >= 0;
      @   ensures (\forall int x; 0 <= x && x < logArray.length; \fresh(logArray[x]));
      @   ensures currentRecord == 0;
      @*/
    public /*@pure@*/ LogFile() {
	int i = 0;
	/*@ loop_invariant 0 <= i && i <= logArray.length
	  @    && (\forall int x; 0 <= x && x < i; logArray[x] != null && \fresh(logArray[x]));
	  @ assignable logArray[*];
	  @ decreases logArray.length - i;
	  @*/
	while(i < logArray.length) {
            logArray[i++] = new LogRecord();
	}
        currentRecord = 0;
    }


    /*@ public normal_behavior 
      @    requires balance >= 0;
      @    requires LogRecord.transactionCounter >= 0;
      @    name "Contract for addRecord";      
      @    assignable currentRecord, 
      @               (\infinite_union int x; 0 <= x && x < logArray.length ? logArray[x].* : \empty),
      @               LogRecord.transactionCounter;
      @    ensures \old(currentRecord) + 1 != logFileSize 
      @            ? currentRecord == \old(currentRecord) + 1 
      @            : currentRecord == 0;
      @    ensures logArray[currentRecord].balance == balance;
      @    ensures LogRecord.transactionCounter >= 0;
      @*/
    public void addRecord(int balance) throws CardException {
	currentRecord++;
	if(currentRecord == logFileSize) {
	    currentRecord = 0;
	}
        logArray[currentRecord].setRecord(balance);
    }


    /*@ public normal_behavior
      @    ensures (\forall int i; 0 <= i && i < logArray.length;
      @                            logArray[i].balance <= \result.balance);
      @ */
    public /*@ pure @*/ LogRecord getMaximumRecord() {
	LogRecord max = logArray[0];
	int i = 1;    
	/*@ loop_invariant 0 <= i && i <= logArray.length 
          @                && max != null 
          @                && (\forall int j; 0 <= j && j < i; 
          @                                   logArray[j].balance <= max.balance);
	  @ assignable \nothing;
	  @ decreases logArray.length - i; 
	  @*/
	while(i < logArray.length) {
	    LogRecord lr = logArray[i++];
	    if(lr.getBalance() > max.getBalance()) {
		max = lr;
	    }        
	}
	return max;
    }


    
    /*@ public normal_behavior
      @ requires a.length > 0;
      @ assignable a[*];
      @ ensures (\forall int i; 0 <= i && i < a.length - 1; a[i] >= a[i + 1]);
      @ */
    void demo(int[] a) {
        int l = a.length;
        int pos = 0;
        /*@ loop_invariant  0 <= pos && pos <= a.length 
          @    && (\forall int x; x >= 0 && x < pos - 1; a[x] >= a[x + 1]) 
          @    && (\forall int x; x >= 0 && x <= pos - 1; 
          @                       (\forall int y; y >= pos && y < a.length; a[x] >= a[y]));
	  @ assignable a[*];
	  @ decreases l - pos; 
	  @*/
        while(pos < l) {
	    int counter = pos;
	    int idx = pos;
	    /*@ loop_invariant pos <= counter && counter <= a.length 
  	      @     && pos <= idx && idx < a.length && pos < a.length 
	      @     && (\forall int x; x >= pos && x < counter; a[idx] >= a[x]);
	      @ assignable \nothing;
	      @ decreases l - counter; 
	      @*/
	    while(counter < l) {
	        if(a[counter] > a[idx]) {
		    idx = counter;
	        }
	        counter = counter + 1;
	    }
  	    int tmp = a[idx];
	    a[idx] = a[pos];
	    a[pos] = tmp;
	    pos = pos + 1;
        }
    }

    
    public static void main(String args[]) {
	LogFile f = new LogFile();
	int[] a = new int[]{3, 1, 7, 5, 4, 0, 6, 4};
	f.demo(a);	
	for(int i = 0; i < a.length; i++) {
	    System.out.print(a[i] + ",");
	}
    }
}
