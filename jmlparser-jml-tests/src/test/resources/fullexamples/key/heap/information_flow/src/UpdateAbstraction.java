//Examples from the paper 
//"Abstract Interpretation of Symbolic Execution with Explicit State Updates"

class UpdateAbstraction {
    
    static int l;
    static int l2;    
    static int h;
    
    //@ static model \locset LOW;           	//just an abbreviation
    //@ static represents UpdateAbstraction.LOW = \set_union(l, l2);
    //@ static model \locset HIGH;           	//just an abbreviation
    //@ static represents UpdateAbstraction.HIGH = \singleton(h);
    
    //@ static ghost \locset pcDep;     //buffer for dependencies of program counter     
    
    //@ static ghost \locset lDep;  //one dep field for every normal field
    //@ static ghost \locset l2Dep; //one dep field for every normal field    
    //@ static ghost \locset hDep;  //one dep field for every normal field
    
    
    /*@ requires UpdateAbstraction.pcDep == \empty;
      @ requires UpdateAbstraction.lDep == \singleton(l);
      @ requires UpdateAbstraction.l2Dep == \singleton(l2); 
      @ requires UpdateAbstraction.hDep == \singleton(h);
      @ ensures \subset(UpdateAbstraction.lDep, UpdateAbstraction.LOW);
      @*/
    static void ex7_1_insecure() {
	//@ set UpdateAbstraction.lDep = \set_union(UpdateAbstraction.pcDep, UpdateAbstraction.hDep); //assignment
	l = h;
    }
    
    
    /*@ requires UpdateAbstraction.pcDep == \empty;
      @ requires UpdateAbstraction.lDep == \singleton(l); 
      @ requires UpdateAbstraction.l2Dep == \singleton(l2);      
      @ requires UpdateAbstraction.hDep == \singleton(h);
      @ ensures \subset(UpdateAbstraction.lDep, UpdateAbstraction.LOW);
      @*/
    static void ex7_2_insecure() {
	//@ set UpdateAbstraction.pcDep = \set_union(UpdateAbstraction.pcDep, UpdateAbstraction.hDep); //entering conditional
	if(h > 0) {
	    //@ set UpdateAbstraction.lDep = UpdateAbstraction.pcDep; //assignment 
	    l = 1;
	} else {
	    //@ set UpdateAbstraction.lDep = UpdateAbstraction.pcDep; //assignment
	    l = 2;
	}
    }
    
    
    /*@ requires UpdateAbstraction.pcDep == \empty;
      @ requires UpdateAbstraction.lDep == \singleton(l); 
      @ requires UpdateAbstraction.l2Dep == \singleton(l2);      
      @ requires UpdateAbstraction.hDep == \singleton(h);
      @ ensures \subset(UpdateAbstraction.lDep, UpdateAbstraction.LOW);
      @*/
    static void ex7_3_secure() {
	//@ set UpdateAbstraction.pcDep = \set_union(UpdateAbstraction.pcDep, UpdateAbstraction.hDep); //entering conditional
	if(l > 0) {
	    //@ set UpdateAbstraction.hDep = UpdateAbstraction.pcDep; //assignment 
	    h = 1;
	} else {
	    //@ set UpdateAbstraction.hDep = UpdateAbstraction.pcDep; //assignment
	    h = 2;
	}
    }   
    
    
    /*@ requires UpdateAbstraction.pcDep == \empty;
      @ requires UpdateAbstraction.lDep == \singleton(l); 
      @ requires UpdateAbstraction.l2Dep == \singleton(l2);      
      @ requires UpdateAbstraction.hDep == \singleton(h);
      @ ensures \subset(UpdateAbstraction.lDep, UpdateAbstraction.LOW);
      @*/
    static void ex7_4_secure() {
	//@ ghost \locset oldPcDep = UpdateAbstraction.pcDep;         //entering conditional
	//@ set UpdateAbstraction.pcDep = \set_union(UpdateAbstraction.pcDep, UpdateAbstraction.hDep); //entering conditional
	if(h > 0) {
	    //@ set UpdateAbstraction.hDep = UpdateAbstraction.pcDep; //assignment 
	    l = 1;
	} else {
	    //@ set UpdateAbstraction.hDep = UpdateAbstraction.pcDep; //assignment
	    l = 2;
	}
	//@ set UpdateAbstraction.pcDep = oldPcDep; //leaving conditional; setting back pcDep is allowed because conditional has no other exit points
	
	//@ set UpdateAbstraction.lDep = UpdateAbstraction.pcDep; //assignment
	l = 3;
    }     
    
    
    /*@ requires UpdateAbstraction.pcDep == \empty;
      @ requires UpdateAbstraction.lDep == \singleton(l);
      @ requires UpdateAbstraction.l2Dep == \singleton(l2);       
      @ requires UpdateAbstraction.hDep == \singleton(h);
      @ ensures \subset(UpdateAbstraction.lDep, UpdateAbstraction.LOW);
      @*/
    static void ex7_5_secure() {
	//@ set UpdateAbstraction.hDep = UpdateAbstraction.pcDep; //assignment
	h = 0;
	
	//@ set UpdateAbstraction.lDep = \set_union(UpdateAbstraction.pcDep, UpdateAbstraction.hDep); 
	l = h;
    } 
    
    
    //different encoding here (following the paper more closely)    
    /*@ requires UpdateAbstraction.lDep == \singleton(l); 
      @ requires UpdateAbstraction.l2Dep == \singleton(l2); 
      @ requires UpdateAbstraction.hDep == \singleton(h);
      @ ensures \subset(UpdateAbstraction.lDep, UpdateAbstraction.LOW);
      @*/
    static void ex7_6_secure() {
	//ghost code for entering conditional----->
	//@ ghost \locset guardDep = UpdateAbstraction.hDep;
	int lOld = l;	
	int hOld = h;
	//<----------------------------------------
	
	if(h > 0) {
	    //@ set UpdateAbstraction.hDep = UpdateAbstraction.lDep; //assignment
	    h = l;
	    //@ set UpdateAbstraction.lDep = UpdateAbstraction.hDep; //assignment
	    l = h;
	}
	
	//ghost code for leaving conditional------>
	if(l != lOld) {
	    //@ set UpdateAbstraction.lDep = \set_union(UpdateAbstraction.lDep, guardDep);
	    ;
	}
	if(h != hOld) {
	    //@ set UpdateAbstraction.hDep = \set_union(UpdateAbstraction.hDep, guardDep);
	    ;
	}
	//<-----------------------------------------
    }        
    
    
    //again the encoding of 7_6 (cannot prove security)
    /*@ requires UpdateAbstraction.lDep == \singleton(l);
      @ requires UpdateAbstraction.l2Dep == \singleton(l2);     
      @ requires UpdateAbstraction.hDep == \singleton(h);
      @ ensures \subset(UpdateAbstraction.lDep, UpdateAbstraction.LOW);
      @*/
    static void ex7_7_secure() {
	//ghost code for entering conditional----->
	//@ ghost \locset guardDep = UpdateAbstraction.hDep;
	int lOld = l;	
	int hOld = h;
	//<----------------------------------------	
	
	if(h > 0) {
	    //@ set UpdateAbstraction.lDep = \empty; //assignment
	    l = 2;	    
	    //@ set UpdateAbstraction.hDep = \empty; //assignment	    
	    h = 2;
	} else {
	    //@ set UpdateAbstraction.lDep = \empty; //assignment	    
	    l = 2;
	    //@ set UpdateAbstraction.hDep = \empty; //assignment	    
	    h = 2;
	}
	
	//ghost code for leaving conditional------>
	if(l != lOld) {
	    //@ set UpdateAbstraction.lDep = \set_union(UpdateAbstraction.lDep, guardDep);
	    ;
	}
	if(h != hOld) {
	    //@ set UpdateAbstraction.hDep = \set_union(UpdateAbstraction.hDep, guardDep);
	    ;
	}
	//<-----------------------------------------
    }         
    
    
    //again the encoding of 7_6 (cannot prove security)
    /*@ requires UpdateAbstraction.lDep == \singleton(l); 
      @ requires UpdateAbstraction.l2Dep == \singleton(l2); 
      @ requires UpdateAbstraction.hDep == \singleton(h);
      @ ensures \subset(UpdateAbstraction.lDep, UpdateAbstraction.LOW);
      @*/
    static void ex7_8_secure() {
	//@ set UpdateAbstraction.lDep = UpdateAbstraction.hDep; //assignment
	l = h - h;
    }         
    
    
    /*@ requires UpdateAbstraction.pcDep == \empty;
      @ requires UpdateAbstraction.lDep == \singleton(l);
      @ requires UpdateAbstraction.l2Dep == \singleton(l2);       
      @ requires UpdateAbstraction.hDep == \singleton(h);
      @ ensures \subset(UpdateAbstraction.lDep, UpdateAbstraction.LOW);
      @ diverges true;
      @*/    
    static void ex9_secure() {
	//@ set UpdateAbstraction.lDep = UpdateAbstraction.pcDep; //assignment
	l = 0;
	//@ set UpdateAbstraction.l2Dep = UpdateAbstraction.pcDep; //assignment
	l2 = 0;
	
	//@ set UpdateAbstraction.pcDep = \set_union(UpdateAbstraction.pcDep, UpdateAbstraction.hDep); //entering loop
	/*@ loop_invariant l2 >= 0;
	  @ assignable l2, \singleton(UpdateAbstraction.l2Dep), h, \singleton(UpdateAbstraction.hDep), \singleton(UpdateAbstraction.pcDep);
	  @*/
	while(h < 0) {
	    //@ set UpdateAbstraction.l2Dep = \set_union(UpdateAbstraction.pcDep, UpdateAbstraction.l2Dep); //assignment
	    l2++;
	    //@ set UpdateAbstraction.hDep = \set_union(UpdateAbstraction.pcDep, UpdateAbstraction.hDep);
	    h++;
	    //@ set UpdateAbstraction.pcDep = \set_union(UpdateAbstraction.pcDep, UpdateAbstraction.hDep); //entering loop again	    
	}
	//@ set UpdateAbstraction.pcDep = \set_union(UpdateAbstraction.pcDep, UpdateAbstraction.l2Dep); //entering conditional
	if(l2 < 0) {
	    //@ set UpdateAbstraction.lDep = UpdateAbstraction.pcDep; //assignment
	    l = 1;
	}
    }
}
