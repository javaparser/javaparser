package MapCaseStudy;

public abstract class AbstractMap implements MapInterface {

    public MapEntry[] entries;

    /*@
    @
    @ public invariant entries.length == \map_size(map);
    @
    @ public invariant !\in_domain(map,null);
    @
    @ public invariant (\forall int i; 0 <= i && i < entries.length; \in_domain(map,entries[i].key));
    @ public invariant (\forall int i; 0 <= i && i < entries.length;
    @                      \map_get(map, entries[i].key) == entries[i].value);
    @
    @ public invariant (\forall Object o; \in_domain(map,o);(
    @       \exists int i; 0 <= i && i < entries.length; o == entries[i].key ));
    @
    @ public invariant (\forall int i1; 0 <= i1 && i1 < entries.length;
    @                      (\forall int i2; 0 <= i2 && i2 < entries.length && i2 != i1;
    @                          ( entries[i1].key != entries[i2].key )));
    @
    @ public invariant \typeof(entries) == \type(MapEntry[]);
    @
    @ public invariant footprint ==
    @      \set_union((\infinite_union int i; 0 <= i && i < entries.length;
    @                          entries[i].*), this.*, entries.*);
    @
    @ public invariant (\forall int i; 0 <= i && i < entries.length; entries[i].key != null);
    @ public invariant (\forall int i; 0 <= i && i < entries.length; entries[i].value != null);
    @ public invariant \domain_implies_created(map);
    @
    @*/
    
    /*@ normal_behaviour
     @ requires target != entries;
     @ requires target != null;
     @ requires 0 <= numberCopies;
     @ requires 0 <= targetIndex && targetIndex + numberCopies <= target.length;
     @ requires 0 <= entriesIndex && entriesIndex + numberCopies <= entries.length;
     @ requires \typeof(target) == \typeof(entries);
     @ ensures (\forall int x; 0 <= x && x < numberCopies; 
     @               ( target[targetIndex + x] == entries[entriesIndex + x]));
     @ ensures (\forall Object o; !\fresh(o));
     @ assignable target[targetIndex..targetIndex + numberCopies - 1];
     @*/
    abstract void copyMapEntries(MapEntry[] /*@nullable*/ target,
            int targetIndex,
            int entriesIndex,
            int numberCopies);
    
    /*@ normal_behavior
     @ ensures \in_domain(map, key) ? 
     @              (\result >= 0 && \result < entries.length && entries[\result].key == key) : 
     @              (\result == -1);
     @ ensures (\forall Object o; !\fresh(o));
     @ accessible footprint;
     @*/
    abstract /*@ strictly_pure */ int getIndexOfKey(Object key);
    
    /*@ normal_behavior
    @ ensures \fresh(\result);
    @ ensures \result.key == key;
    @ ensures \result.value == value;
    @*/
    abstract /*@ pure */ MapEntry newMapEntry(Object key, Object value);

    /*@ normal_behavior
     @   requires l >= 0;
     @   ensures \typeof(\result) == \type(MapEntry[]);
     @   ensures \result.length == l;
     @   ensures \fresh(\result);
     @   ensures \result != null;
     @   ensures (\forall int i; 0 <= i && i < \result.length; \result[i] == null);
     @*/
    abstract /*@ pure nullable */ MapEntry[] newMapEntryArray(int l);
    
    /*@ normal_behaviour
     @ ensures \result.length == entries.length + 1;
     @ ensures (\forall int i; 0 <= i && i < entries.length; \result[i] == entries[i]);
     @ ensures \result[entries.length].key == key;
     @ ensures \result[entries.length].value == value;
     @ ensures \fresh(\result, \result[entries.length]);
     @ ensures !\in_domain(map, \result);
     @ ensures !\in_domain(map, \result[entries.length]);
     @ ensures \typeof(\result) == \type(MapEntry[]);
     @*/
    abstract /*@ pure */ MapEntry[] putExtendArray(Object key, Object value);

    /*@ normal_behaviour
     @ requires 0 <= index && index < entries.length;
     @ ensures map == \map_update(\old(map), entries[index].key, value);
     @ ensures \result == (\map_get(\old(map), entries[index].key));
     @ ensures (\forall Object o; !\fresh(o));
     @ assignable entries[index].value, map;
     @*/
    abstract Object putInDomain(int index, Object value);

    /*@ normal_behaviour
     @ requires !\in_domain(map, key);
     @ ensures map == \map_update(\old(map), key, value);
     @ ensures \result == null;
     @ ensures \fresh(entries, entries[entries.length - 1]);
     @ assignable footprint;
     @*/
    abstract /*@ nullable */ Object putNotInDomain(Object key, Object value);

    /*@ normal_behaviour
     @ requires newEntries != null;
     @ requires newEntries != entries;
     @ requires entries.length > 0;
     @ requires newEntries.length == entries.length - 1;
     @ requires \typeof(newEntries) == \typeof(entries);
     @ requires 0 <= index && index < entries.length;
     @ ensures (\forall Object o; !\fresh(o));
     @ ensures (\forall int i; 0 <= i && i < newEntries.length;
     @               newEntries[i] == ((i < index) ? entries[i] : entries[i + 1]));
     @ assignable newEntries[*];
     @*/
    abstract void removeCopyOldEntries( /*@ nullable */ MapEntry[] newEntries, int index);
    
    /*@ normal_behaviour
     @ requires 0 <= index && index < entries.length;
     @ ensures \result.length == entries.length - 1;
     @ ensures \typeof(\result) == \type(MapEntry[]);
     @ ensures (\forall int i; 0 <= i && i < \result.length;
     @               \result[i] == ((i < index) ? entries[i] : entries[i + 1]));
     @ ensures \fresh(\result);
     @*/
    abstract /*@ pure */ MapEntry[] removeGetNewArray(int index);

    /*@ normal_behaviour
     @ requires 0 <= index && index < entries.length;
     @ ensures map == \map_remove(\old(map), \old(entries[index].key));
     @ ensures \result == \map_get(\old(map), \old(entries[index].key));
     @ ensures \fresh(entries);
     @ assignable footprint;
     @*/
    abstract Object removeInDomain(int index);
    
    /*@ normal_behaviour
     @ requires 0 <= index && index < entries.length;
     @ ensures map == \map_remove(\old(map), \old(entries[index].key));
     @ ensures \fresh(entries);
     @ assignable footprint;
     @*/
    abstract void removeInDomainWithoutResult(int index);
    
    /*@ normal_behaviour
     @ requires 0 <= index && index < entries.length;
     @ requires (\forall int i; 0 <= i && i < newEntries.length;
     @               newEntries[i] == ((i < index) ? entries[i] : entries[i + 1]));
     @ requires \typeof(newEntries) == \type(entries);
     @ requires newEntries.length == entries.length - 1;
     @ ensures map == \map_remove(\old(map), \old(entries[index].key));
     @ ensures (\forall Object o; !\fresh(o));
     @ ensures entries == newEntries;
     @ assignable footprint;
     @*/
    abstract void removeSetEnries(MapEntry[] newEntries, int index);

}
