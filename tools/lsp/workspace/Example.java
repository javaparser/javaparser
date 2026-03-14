//-*- jml-keys: openjml

public class Example {
    /*+key@ public invariant 2*a == invariant;*/    
    /*+openjml@ public invariant stupid_name : 2*a == invariant;*/
    /*@ public invariant 2*a == invariant;*/    

    public int foo = 2;

    /*@
    model_behavior
    requires req1 : true;
    ensures true;
    assignable \nothing;
    public model int bar(int a);
    */
}
 