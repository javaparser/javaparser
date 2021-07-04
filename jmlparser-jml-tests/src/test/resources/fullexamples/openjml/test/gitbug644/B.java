//@ non_null_by_default
public class B {
    public B() { }

    /*@ immutable pure public static model class Content {

       function helper
       public Object mapsObject(nullable Object key);

       function helper
       public Object mapss(nullable Object key);

       function helper
       public boolean hasMapObject(nullable Object key);

       function helper
       public boolean hasMap(nullable Object key);
     }
    @*/

  //@ axiom (\forall Content c; (\forall Object o; c.hasMapObject(o) ==> c.mapsObject(o) == c.mapss(o)) && c.hasMapObject(null) ==> c.mapsObject(null) == c.mapss(null));
  //@ axiom (\forall Content c; (\forall Object o; o != null; c.hasMapObject(o) ==> c.mapsObject(o) == c.mapss(o)));
  //@ axiom (\forall Content c; c.hasMapObject(null) ==> c.mapsObject(null) == c.mapss(null));
}
