public class User {

    /*@ spec_public @*/ private int age;

    //@ public invariant 0 <= age && age < 150;
    
    //@ ensures age == 0;
    public User() {
    }
    
    /*@ public normal_behavior
      @   requires 0 <= newAge && newAge < 150;
      @   assignable age;
      @   ensures age == newAge;
      @   ensures \result == this;
//      @ also
//      @ public exceptional_behavior
//      @   requires newAge < 0 || newAge >= 150;
//      @   signals_only Exception;
      @*/
    public User setAge(int newAge) throws Exception {
        if (newAge < 0 || newAge >= 150) {
            throw new Exception("Age out of bounds.");
        }
        this.age = newAge;
        return this;
    }
}