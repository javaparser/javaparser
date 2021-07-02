final class ArrayList {
    
    //@ model \locset footprint;
    //@ accessible footprint: footprint;
    //@ accessible \inv: footprint;
    
    
    private /*@nullable@*/ Object[] array = new Object[10];
    private int size = 0;
    
    private int notPartOfFootprint;
    
    //@ represents footprint = array, array[*], size;    
    
    //@ invariant array != null;
    //@ invariant 0 <= size && size <= array.length;
    //@ invariant \typeof(array) == \type(Object[]);
    
    //@ static ghost \locset resultDep; //buffer for dependencies of return value

    
    //@ ghost \locset sizeDep;        //one dep field for every normal field
    //@ ghost \locset arrayDep;       //one dep field for every normal field    
    //@ ghost \locset arraySlotDep[]; //one dep field for every normal field
    
        
    //contract encodes "accessible footprint;"
    /*@ normal_behaviour 
      @   requires \inv; 
      @   requires arrayDep == \singleton(array);
      @   requires sizeDep == \singleton(size);
      @   requires (\forall int i; arraySlotDep[i] == \singleton(array[i]));
      @   requires (\forall int i; arraySlotDep.length == array.length);
      @   ensures \subset(ArrayList.resultDep, \old(footprint));
      @   diverges true;
      @*/    
    public /*@helper@*/ boolean contains(/*@nullable@*/ Object o) {
	//@ ghost \locset pcDep = \empty;
	//@ ghost \locset oDep = \empty;
	
	//@ ghost \locset iDep = pcDep; //assignment
	int i = 0;
	
	//@ set pcDep = \set_union(pcDep, \set_union(iDep, sizeDep)); //entering loop
	
	/*@ loop_invariant 0 <= i && i <= size
	  @    && \subset(pcDep, \old(footprint))
	  @    && \subset(iDep, \old(footprint));
	  @ assignable \nothing;
	  @ decreases size - i;
	  @*/
	while(i < size) {
	    //@ set pcDep = \set_union(pcDep, \set_union(arrayDep, \set_union(iDep, \set_union(oDep, arraySlotDep[i])))); //entering conditional
	    if(array[i] == o) {
		//@ set ArrayList.resultDep = pcDep; //return
		return true;
	    }
	    
	    //@ set iDep = \set_union(pcDep, iDep); //assignment
	    i++;
	    
	    //@ set pcDep = \set_union(pcDep, \set_union(iDep, sizeDep)); //entering loop again
	    ; //workaround for RecodeR bug
	}
	
	//@ set ArrayList.resultDep = pcDep; //return
	return false;
    }

    
    //contract encodes "accessible footprint" with precondition "0 <= index && index < size()"
    /*@ normal_behaviour
      @   requires \inv; 
      @   requires 0 <= index && index < size();
      @   requires arrayDep == \singleton(array);
      @   requires sizeDep == \singleton(size);
      @   requires (\forall int i; arraySlotDep[i] == \singleton(array[i]));
      @   requires (\forall int i; arraySlotDep.length == array.length);                                                                                                                                                                
      @   ensures \subset(ArrayList.resultDep, \old(footprint));
      @*/    
    public /*@nullable helper@*/ Object get(int index) {
	//@ ghost \locset pcDep = \empty;
	//@ ghost \locset indexDep = \empty;
	
	//@ set pcDep = \set_union(indexDep, sizeDep); //entering conditional
	if(index < 0 || size <= index) {
	    //@ set ArrayList.resultDep = pcDep; //return
	    throw new IndexOutOfBoundsException();
	}
	
	//@ set ArrayList.resultDep = \set_union(pcDep, \set_union(arrayDep, \set_union(indexDep, arraySlotDep[index]))); //return
	return array[index];
    }
    
    
    //contract encodes "accessible footprint"
    /*@ normal_behaviour
      @   requires \inv;
      @   requires arrayDep == \singleton(array);
      @   requires sizeDep == \singleton(size);
      @   requires (\forall int i; arraySlotDep[i] == \singleton(array[i]));
      @   requires (\forall int i; arraySlotDep.length == array.length);                                                                                                                                               
      @   ensures \subset(ArrayList.resultDep, \old(footprint));
      @*/
    public /*@helper@*/ int size() {
	//@ ghost \locset pcDep = \empty;	
	
	//@ set ArrayList.resultDep = \set_union(pcDep, sizeDep);
	return size;
    }
}
