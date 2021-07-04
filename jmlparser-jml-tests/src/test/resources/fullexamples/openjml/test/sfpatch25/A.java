class A {

	//@ ensures false;
private void test17a(){

        int a = 2;
        int b = 2;

    test17Helper1(a,b);   //OK
    test17Helper1(a,b,b); // Compiler crash
}

private void test17Helper1(/*@ non_null */ int a, /*@ non_null */ int ...other){}

}