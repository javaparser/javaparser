// This class tests that jmldoc knows how to print all kinds of expressions
import org.jmlspecs.annotation.*;

public class PP extends QQ {

   //@ pure
    int m() { return 0; }
    
    @Pure
    int mq(int a, boolean b, Object o) { return 0; }
    
    //@ invariant i + 2 * 3 - 4 / 5 + 6 % i + (i << 5) + (i >> 6) + (i >>> i) == -10;
    //@ invariant i > 0 && i < 0 && i == 0 && (i <= +10 ? i >= 0 : i != 0);
    //@ invariant b || !b && (b ==> b) && ( b <==> b ) && ( b <=!=> b ) && (b <== b);
    //@ invariant (i & 1) + (i ^ 1) + (i | 1) + (~i) == 0;
    
    //@ invariant \type(int) <: \typeof(o);
    //@ invariant \type(int) <#= \typeof(o);
    //@ invariant \type(int) <# \typeof(o);
    //@ invariant o instanceof java.lang.String;
    
    //@ invariant true && false && (i == 10.0) && (i < -10e4) && (i > +.4e+5) && (i > +.4e+50);
    //@ invariant "asd" != (Object)null && 'c' != 'd' && 'a' != '\045' && "45" != "\n\"'\034";
    //@ invariant (int)9 == 9 && (char)3 == 'd' && (float)4 == (double)5 && (short)1 == (byte)(-1) && (long)-13 == -12;
    
    //@ invariant (new int[]{1,2,3}).length == 3 && (new int[]{1,2,3})[0] == 1 && a[3] == 6;
    //@ invariant (new PP()).i == 0;
    //  FIXME @ invariant (new PP() { int m() { return 5; } }) != null;
    
    //@ invariant (\forall int i; i != 0) && (\forall int k; k > 0; k >-1);
    //@ invariant (\exists int i; i != 0) && (\exists int k; k > 0; k >-1);
    //@ invariant (\num_of int i; i == 0) == (\num_of int k; k > 0; k >-1);
    //@ invariant (\max int i; i>0 && i<10; i ) == (\min int i; i>0 && i<10; i );
    //@ invariant (\sum int i; i>0 && i<10; i ) == (\product int i; i>0 && i<10; i );
    //@ invariant this.i == 0 && super.bb() && PP.class != null;
    //@ invariant (* informal predicate *) && false && m() == 0 && 0==mq(1,false,new Object());
    //@ invariant \is_initialized(PP);
    //@ invariant \is_initialized(Integer);
    //@ invariant \invariant_for(o);
    //@ invariant (\lblpos A true);
    //@ invariant (\lblneg A true);
    //@ invariant (\lbl A true);
    //@ invariant ! \reach(o).isEmpty();
    //@ invariant \reach(o) != null;
    //@ invariant (new PP() { int m() { return 5; } }) != null;
    //@ invariant new JMLSetType { Integer o | list.contains(o) && o > 0 } != null;
    // NOTE: \old with 2 arguments and \pre is only within a method
    
    //@ constraint i >= \old(i);
    //@ axiom true;
    //@ initially true;
    //@ readable i if true;
    //@ writable i if true;
    //@ monitors_for i = o;

    //@ public invariant false;
    //@ public constraint i >= \old(i);
    //@ public initially true;
    //@ public readable i if true;
    //@ public writable i if true;
    //@ public monitors_for i = o;

    //@ model int modelM;
    //@ represents modelM = 20;
    
    //@ model int modelMZ;
    //@ private represents modelMZ = 20;
    
    //@ model int modelM2; in modelM;
    //@ ensures \result > 0 && ! \nonnullelements(a) && \elemtype(\typeof(a)) == \type(int);
    //@ ensures \duration(m()) > 0 && \space(o) > 0 && \working_space(m()) > 0;
    //@ ensures \fresh(a) && \fresh(a,o);
    //@ ensures \max(\lockset) == a;
    //@ ensures \max(\lockset).hashCode() != 0;
    //@ ensures \not_modified(i,o);
    //@ ensures \not_modified(a[1 ..*]);
    //@ ensures \not_assigned(\nothing) || \only_accessed(\nothing) || \only_captured(\nothing) || \only_assigned(\nothing);
    //@ ensures \not_assigned(\everything) || \only_accessed(\everything) || \only_captured(\everything) || \only_assigned(\everything);
    //@ ensures \not_assigned(i) || \only_accessed(i) || \only_captured(i) || \only_assigned(i);
    //@ ensures \not_assigned(i,a[1 ..*]) || \only_accessed(i,a[1 ..]) || \only_captured(i,a[*]) || \only_assigned(i,o.*);
    //@ ensures \not_assigned(\not_specified) || \only_accessed(\not_specified) || \only_captured(\not_specified) || \only_assigned(\not_specified);
    // FIXME @ ensures \only_called(m,mq);
    int mm() { return 3; }
    
    //@ requires \same;
    //@ requires true; pre true;
    //@ ensures false; post true;
    //@ signals (Exception e) true; exsures (Exception) false;
    //@ signals_only Exception;
    //@ diverges true;
    //@ modifies i;
    //@ assignable \nothing;
    //@ assignable p.i,p.*,this.*,super.*,PP.*;
    //@ modifiable i,o,a,a[*],a[1],a[1 .. 2],a[1 ..],a[1 ..*];
    // @ modifiable a[1..2],a[1..*],a[1..]; // FIXME (white space before ..)
    //@ assignable \everything;
    //@ accessible \nothing;
    //@ accessible \everything;
    //@ accessible i, PP.*;
    //@ callable \nothing;
    //@ callable \everything;
    //@ callable m, mq, mq(int, boolean, Object), bb, super.bb, o.m();  // FIXME _ more?
    //@ measured_by 10;
    //@ measured_by 20 if false;
    //@ captures i, a[*];
    //@ captures \nothing;
    //@ captures \everything;
    //@ duration 0;
    //@ duration 0 if true;
    //@ working_space 0;
    //@ working_space 0 if true;
    //@ when false;
    void qq() {}

    //@ signals_only Exception, java.lang.RuntimeException;
    void qq1() {}
    
    //@ signals_only \nothing;
    void qq2() {}
    
    //@ requires \not_specified;
    //@ ensures \not_specified;
    //@ diverges \not_specified;
    //@ signals (Exception) \not_specified;
    // NOT_JML: @ signals_only \not_specified;
    //@ assignable \not_specified;
    //@ accessible \not_specified;
    //@ callable \not_specified;
    //@ when \not_specified;
    //@ measured_by \not_specified;
    //@ duration \not_specified;
    //@ working_space \not_specified;
    //@ captures \not_specified;
    void sp() {}

    int i;
    boolean b;
    Object o;
    PP p; //@ maps p.i \into modelM;
    int a[] = new int[10];
    java.util.List list;
    
    /*@ public normal_behavior
    @      requires true;
    @      {|
    @          ensures false;
    @          diverges true;
    @      also
    @          ensures true;
    @          diverges true;
    @      |}
    @  also protected exceptional_behavior
    @       forall Object o;
    @       old int j = k+1;
    @      requires false;
    @      signals (Exception) true;
    @  also code behavior
    @      requires false;
    @      signals (Exception) true;
    @  also private code model_program {
        }
    @  also model_program {
            int x = 0;
            x++;
            ++x;
            x--;
            --x;
            x = 1;
            x += 1;
            x -= 1;
            x *= 1;
            x /= 1;
            x %= 1;
            x <<= 1;
            x >>= 1;
            x >>>=1 ;
            x |= 1;
            x &= 1;
            x ^= 1;
            if (true) x = 1;
            if (true) { x = 1; } else { x = 2; }
            while (true) { x = 1; if (x == 2) continue; if (x == 3) break; }
            do x = 1; while (true);
            switch (x) { case 1: x=2; break; default: x=3; }
            ;
            assume true;
            assert true;
            choose { x = 1; } or { x = 2; }
            choose_if { x = 1; } or { x = 2; } else { x = 3; }
            behavior requires true; ensures false;
            abrupt_behavior requires false; continues true; breaks true; returns true;
            invariant false;

            // FIXME - add loop invariants, refining statements, try catch finally blocks,
            // model programs do not need: set, debug, ghost decls
    @  }
   */
   void z(int k) {} 
   
   // Various combinations of javadoc comments, tags, and jml
   
   // nothing
   public void q0(int i) {}
   
   /** Javadoc comment only.  Second sentence. */
   public void q1(int i) {}
   
   /** @param i tag only */
   public void q2(int i) {}
   
   /** Javadoc comment and tag.  Second sentence.
    * @param i tag comment
    */
   public void q3(int i) {}
   
   //@ requires i > 0;
   public void q4(int i) {}
   
   //@ requires i > 0;
   /** Javadoc comment and JML.  Second sentence. */
   public void q5(int i) {}
   
   //@ requires i > 0;
   /** @param i tag and JML*/
   public void q6(int i) {}
   
   //@ requires i > 0;
   /** Javadoc comment and tag and JML.  Second sentence.
    * @param i tag comment
    */
   public void q7(int i) {}
   
   // nothing
   //@ model public void mq0(int i) {}
   
   /** Javadoc comment only.  Second sentence. */
 //@ model public void mq1(int i) {}
   
   /** @param i tag only */
 //@ model public void mq2(int i) {}
   
   /** Javadoc comment and tag.  Second sentence.
    * @param i tag comment
    */
 //@ model public void mq3(int i) {}
   
   //@ requires i > 0;
 //@ model public void mq4(int i) {}
   
   //@ requires i > 0;
   /** Javadoc comment and JML.  Second sentence. */
 //@ model public void mq5(int i) {}
   
   //@ requires i > 0;
   /** @param i tag and JML*/
 //@ model public void mq6(int i) {}
   
   //@ requires i > 0;
   /** Javadoc comment and tag and JML.  Second sentence.
    * @param i tag comment
    */
 //@ model public void mq7(int i) {}
   
   /** Javadoc comment and JML.  Second sentence. */
   //@ requires i > 0;
 //@ model public void mmq5(int i) {}
   
   /** @param i tag and JML*/
   //@ requires i > 0;
 //@ model public void mmq6(int i) {}
   
   /** Javadoc comment and tag and JML.  Second sentence.
    * @param i tag comment
    */
   //@ requires i > 0;
 //@ model public void mmq7(int i) {}
   
   // FIXME - q4 is not indented correctly
   // FIXME - extra blank line whenever there are no tags
   // FIXME - model methods have no tags
   
    // FIXME - rationalize handling of precedence and () between Pretty and JmlPretty
    // TODO - implement choose and choose_if from model program
   // FIXME - breaks and continues model program statements all allowed to have labels.
   // FIXME - pretty printing assert and assume in model programs

   // TODO: forall and old in method specs
   
   // TODO: need to test all kinds of statements, including JML statements
   //       labelled, synchronized, throw, local decl, local class,
   //       annotated loops, break (to label), continue (to label), return (with value)
   //       java assert
   //   JML: assert, assume, assert_redundantly, set, debug, unreachable, hence_by
   //   JML: choice, choice_if
   //   UNDERSTAND: invariant in model program
   
   // TODO: example, implies_that
   
    // TODO:  .this  .super .new-expr
    
    // TODO: callable clause, \only_called
    // TODO: long lines, retain user formatting
}

class QQ {
    boolean bb() { return true; }
    int qq;
}
