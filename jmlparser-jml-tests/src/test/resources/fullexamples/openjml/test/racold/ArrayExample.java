public class ArrayExample {
    private /*@ spec_public */ Integer[] someArray;

    public ArrayExample(){
        someArray = new Integer[2];
        someArray[0] = 1;
        someArray[1] = 4;
    }

    //@ ensures \old(someArray[\result]) == 4;
    //@ ensures \old(someArray[\result] + 2) == 6;
    //@ ensures \old(someArray[\result])+ 2 == 6;
    public int someMethod(){
        return 1;
    }

    public static void main(String[] args){
        ArrayExample example = new ArrayExample();
        example.someMethod();
    }

}
