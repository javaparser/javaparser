// This example fails to prove a number of postconditions be\cause stratic tyupes are used to resolve
// the model field _base. If tighter types are used in from and add in the childe classes, then all is OK.
// We will leave this behavior as acceptabble for now. (FIXME)

//@ non_null_by_default
@org.jmlspecs.annotation.CodeBigintMath @org.jmlspecs.annotation.SpecBigintMath
abstract public class MultipleModel {

   //@ public model int _base;
    
    //@ public normal_behavior ensures true; pure
    public MultipleModel() {}
    
   //@ public normal_behavior ensures \result._base == i; pure
   public static MultipleModel from(int i) { // Uses static type
      return new Child1(i);
   }

   //@ public normal_behavior ensures \result._base == this._base + i;
   abstract public MultipleModel add(int i);

   //@ public normal_behavior ensures \result == _base; pure
   abstract public int toInt();
}

//@ non_null_by_default
@org.jmlspecs.annotation.CodeBigintMath @org.jmlspecs.annotation.SpecBigintMath
class Child1 extends MultipleModel {

   public int value1; //@ in _base;
   //@ public represents _base = value1;

   //@ public normal_behavior ensures value1 == i; pure  // value1 here instead of _base -- what is to tell the value of _base?
   public Child1(int i) {
      value1 = i;
   }

   @Override
   public MultipleModel add(int i) {  // Uses static type
      return new Child2(value1 + i);
   }

   @Override
   public int toInt() {
      return value1;
   }
}

//@ non_null_by_default
@org.jmlspecs.annotation.CodeBigintMath @org.jmlspecs.annotation.SpecBigintMath
class Child2 extends MultipleModel {
   public int value2; //@ in _base;
   //@ public represents _base = value2;

   //@ public normal_behavior ensures value2 == i; pure  // Uses value2 instead of _base here
   public Child2(int i) {
      value2 = i;
   }

   @Override
   public MultipleModel add(int i) {   // Uses static type
      return new Child2(value2 + i);
   }

   @Override
   public int toInt() {
      return value2;
   }
}
