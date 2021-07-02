class MySubclass extends MyClass {
    
    Object o;
    //@ represents footprint = this.*, o.*;
    
    
    int add27(int i) {
	return attr = 27 + i;
    }
    
    
    int x;
    int y;
    //@ model int modelField;    
    //@ represents modelField = x + y;
    int test;
    
    /*@ assignable x, y;
      @ ensures modelField == \old(modelField) + 2;
      @*/
    void changeModelField() {
	x++;
	y++;
    }   
}
