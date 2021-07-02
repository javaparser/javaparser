/* These examples can be used to analyze the test coverage achieved KeYTestGen 2.0.
 In particular, to achieve MC/DC coverage, the Proof splitting must be set to "Free" in the Proof Strategy Settings.
Author: Christoph Gladisch
*/

final class CoverageTest { 

 public void foo(){ };
 
 /*@ public normal_behaviour
   requires true;
   ensures true;
 @*/ 
 public void test1(boolean a, boolean b){
  if(a && b){
    foo();
  }
 } 

 
 /*@ public normal_behaviour
   requires true;
   ensures true;
 @*/ 
 public void test2(boolean a, boolean b, boolean c){
  if((a && b) || (a && c) || (b && c)){
    foo();
  }
 } 
 
}