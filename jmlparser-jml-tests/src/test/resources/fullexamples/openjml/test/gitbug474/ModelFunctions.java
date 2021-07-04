public class ModelFunctions {   
    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures true;
      @ public function static model pure int chomp(int i);
      @*/

    //@ axiom \forall int i, j; 489 <= i && i < 526 && 0 <= j && j < 10; i == j ==> chomp(i) == chomp(j);

    public static void main(String[] args) {
        //@ ghost int a = chomp(500);
        //@ ghost int b = chomp(500);
        //@ assert a == b;
    }
}

// This example fails with -minQuant without the 'function' attribute 
// The reason is that chomp is not then specified to be deterministic.