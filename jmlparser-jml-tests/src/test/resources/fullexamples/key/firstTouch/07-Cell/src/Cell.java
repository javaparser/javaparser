class Cell {
    private int x;
    
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures getX() == 0;
      @ ensures \fresh(footprint);
      @*/
    Cell() {
    }
    
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ accessible footprint;
      @ ensures \result == getX();
      @*/
    int getX() {
	return x;
    }
    
    
    /*@ normal_behavior
      @ assignable footprint;
      @ ensures getX() == value;
      @ ensures \new_elems_fresh(footprint); 
      @*/
    void setX(int value) {
	x = value;
    }
    
    /*@ model \locset footprint;
      @ accessible footprint: footprint;
      @ represents footprint = x;
      @*/
    
    //@ accessible \inv: \nothing;
}
