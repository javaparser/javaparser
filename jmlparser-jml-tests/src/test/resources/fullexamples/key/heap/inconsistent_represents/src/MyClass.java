class MyClass {
    //@ model int size;
    //@ represents size = size + 1;
    
    //@ model int evil;
    //@ represents evil \such_that false;
    
    //@ ensures \result == 0;
    int m() {
	return 27;
    }
    

    //@ requires size != evil;
    //@ ensures \result == 0;
    int n() {
	return 27;
    }
}
