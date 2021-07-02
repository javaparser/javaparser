package MapCaseStudy;

public interface MapInterface {

    //@ public ghost instance \locset footprint;
    //@ public ghost instance \map map;
    //@ public instance invariant \subset(\singleton(this.map), footprint);
    //@ public instance invariant \subset(\singleton(this.footprint), footprint);
    //@ public instance invariant \is_finite(map);
    
    // --------
    // Method signatures and specifications
    // --------
    
    /*@ normal_behaviour
     @ ensures map == \map_empty;
     @ assignable footprint;
     @*/
    public void clear();

    /*@ normal_behaviour
     @ ensures \result == \in_domain(map, key);
     @ accessible footprint;
     @*/
    public /*@ pure @*/ boolean containsKey(Object key);

    /*@ normal_behaviour
     @ ensures \result == (\exists Object key; \in_domain(map,key); \map_get(map,key) == value);
     @ accessible footprint;
     @*/
    public /*@ pure @*/ boolean containsValue(Object value);

    /*@ normal_behaviour
     @ ensures \result == (\in_domain(map, key) ? \map_get(map, key) : null);
     @ accessible footprint;
     @*/
    public /*@ pure nullable @*/ Object get(Object key);

    /*@ normal_behaviour
     @ ensures \result == (map == \map_empty);
     @ accessible footprint; 
     @*/
    public /*@ pure @*/ boolean isEmpty();

    /*@ normal_behaviour
     @ ensures map == \map_update(\old(map), key, value);
     @ ensures \result == (\in_domain(\old(map), key) ? \map_get(\old(map), key) : null);
     @ assignable footprint;
     @*/
    public /*@ nullable @*/ Object put(Object key, Object value);

    /*@ normal_behaviour
     @ ensures map == \map_remove(\old(map), key);
     @ ensures \result == (\in_domain(\old(map), key) ? \map_get(\old(map), key) : null);
     @ assignable footprint;
     @*/
    public /*@ nullable @*/ Object remove(Object key);

    /*@ normal_behaviour
     @ ensures \result == \map_size(map);
     @ accessible footprint;
     @*/
    public /*@ pure @*/ int size();

}
