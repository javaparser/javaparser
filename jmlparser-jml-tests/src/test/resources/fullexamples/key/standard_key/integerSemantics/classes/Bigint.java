// please use faithful Java int semantics for this one
class Bigint {
  //@ ghost \bigint x;
  //@ ghost \bigint y;

  //@ ensures x > 0;
  //@ ensures y < 0;
  void foo(){
   //@ set x = 444444444444444444444444444444444;
   //@ set y = (int) x * 4444444444444444;
   //@ set x = x * 4444444444444444;
   {}
  }
}
