public class ExampleObserver implements Observer {
    
    private ExampleSubject subj;
    private int cache;
    
    //@ represents subject = subj;
    //@ represents upToDate = (cache == subj.value());
    
    /*@ public normal_behaviour
      @   ensures subject == s;            
      @*/
    /*@pure@*/ public ExampleObserver(ExampleSubject s) {
	this.subj = s;
    }
    
    
    public void update() {
	cache = subj.value();
    }
    
    
    /*@ public normal_behaviour
      @   requires upToDate;
      @   ensures \result == ((ExampleSubject)subject).value();
      @*/
    /*@pure@*/ public int value() {
	return cache;
    }
}
