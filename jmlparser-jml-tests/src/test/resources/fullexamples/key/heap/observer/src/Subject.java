public abstract class Subject {
    protected /*@spec_public@*/ Observer[] observers = new Observer[0];
    
    //@ public model \locset footprint;
    //@ accessible \inv: footprint, observers, observers.*, (\infinite_union int i; 0 <= i && i < observers.length ? observers[i].* : \empty);
    //@ accessible footprint: footprint;
    
    /*@ public invariant \disjoint(footprint, \set_union(observers, observers[*]));
      @ public invariant (\forall int i; 0 <= i && i < observers.length; 
      @                                  observers[i].\inv 
      @                                  && observers[i].subject == this
      @                                  && observers[i] != this 
      @                                  && \disjoint(observers[i].*, footprint));
      @*/
    

    /*@ public normal_behaviour
      @   requires o.\inv && o.subject == this && o != this && \disjoint(o.*, footprint);
      @   assignable observers;
      @   ensures observers.length == \old(observers.length) + 1;
      @   ensures observers[observers.length - 1] == o;
      @   ensures (\forall int i; 0 <= i && i < observers.length - 1; observers[i] == \old(observers[i]));
      @*/
    public final void addObserver(Observer o) {
	final Observer[] newArr = new Observer[observers.length + 1];
	/*@ loop_invariant 0 <= i && i <= observers.length
	  @                && (\forall int x; 0 <= x && x < i; newArr[x] == observers[x]);
	  @ assignable newArr[*];
	  @ decreases observers.length - i;
	  @*/
	for(int i = 0; i < observers.length; i++) {
	    newArr[i] = observers[i];
	}
	newArr[newArr.length - 1] = o;
	observers = newArr;
    }
    

    /*@ public normal_behaviour
      @   assignable (\infinite_union int x; 0 <= x && x < observers.length ? observers[x].* : \empty);
      @   ensures (\forall int i; 0 <= i && i < observers.length; observers[i].upToDate && observers[i].\inv);
      @*/
    public final void notifyObservers() {
	/*@ loop_invariant 0 <= i && i <= observers.length
	  @                && (\forall int x; 0 <= x && x < observers.length; observers[x].\inv)
	  @                && (\forall int x; 0 <= x && x < observers.length; observers[x].subject == this)
	  @                && (\forall int x; 0 <= x && x < i; observers[x].upToDate);
	  @ assignable (\infinite_union int x; 0 <= x && x < observers.length ? observers[x].* : \empty);
	  @ decreases observers.length - i; 
	  @*/
	for(int i = 0; i < observers.length; i++) {
	    observers[i].update();
	}
    }
}
