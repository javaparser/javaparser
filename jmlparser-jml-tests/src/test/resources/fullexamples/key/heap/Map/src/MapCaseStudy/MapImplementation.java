package MapCaseStudy;

final class MapImplementation extends AbstractMap {

    /*@ normal_behaviour
     @ ensures map == \map_empty;
     @*/
    public /*@pure@*/ MapImplementation() {
        entries = new MapEntry[0];
        //@ set map = \map_empty;
        //@ set footprint = \set_union(\all_fields(this), \all_fields(entries));
    }
    
    public void clear() {
        entries = new MapEntry[0];
        //@ set map = \map_empty;
        //@ set footprint = \set_union(\all_fields(this), \all_fields(entries));
    }
    
    public boolean containsKey(Object key) {
        return getIndexOfKey(key) != -1;
    }

    public boolean containsValue(Object value) {
        /*@ loop_invariant 0 <= i && i <= entries.length;
         @ loop_invariant (\forall int x; 0 <= x && x < i; value != entries[x].value);
         @ decreases entries.length - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < entries.length; i++) {
            if (value == entries[i].value) {
                return true;
            }
        }
        return false;
    }
    
    void copyMapEntries(MapEntry[] target,
            int targetIndex,
            int entriesIndex,
            int numberCopies) {
        /*@ loop_invariant 0 <= i && i <= numberCopies;
         @ loop_invariant (\forall int x; 0 <= x && x < i; 
         @               ( target[targetIndex + x] == entries[entriesIndex + x] ));
         @ loop_invariant (\forall Object o; !\fresh(o));
         @ decreases numberCopies - i;
         @ assignable target[targetIndex..targetIndex + numberCopies - 1];
         @*/
        for (int i = 0; i < numberCopies; i++) {
            target[targetIndex + i] = entries[entriesIndex + i];
        }
    }

    public Object get(Object key) {
        int index = getIndexOfKey(key);
        if (index == -1) {
            return null;
        } else {
            return entries[index].value;
        }
    }

    int getIndexOfKey(Object key) {
        /*@ loop_invariant 0 <= i && i <= entries.length;
         @ loop_invariant (\forall int x; x>=0 && x<i; entries[x].key != key);
         @ loop_invariant (\forall Object o; !\fresh(o));
         @ decreases entries.length - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < entries.length; i++) {
            if (key == entries[i].key) {
                return i;
            }
        }
        return -1;
    }

    public boolean isEmpty() {
        return entries.length == 0;
    }
    
    MapEntry newMapEntry(Object key, Object value) {
        return new MapEntry(key, value);
    }

    MapEntry[] newMapEntryArray(int l) {
        // This function is modeled after ArrayList.newArray()
        return new MapEntry[l];
    }

    public Object put(Object key, Object value) {
        int index = getIndexOfKey(key);
        if (index == -1) {
            return putNotInDomain(key, value);
        } else {
            return putInDomain(index, value);
        }
    }
   
   MapEntry[] putExtendArray(Object key, Object value) {
        MapEntry[] result = newMapEntryArray(entries.length + 1);
        copyMapEntries(result, 0, 0, entries.length);
        result[entries.length] = newMapEntry(key, value);
        return result;
    }

    Object putInDomain(int index, Object value) {
        Object result = entries[index].value;
        entries[index].value = value;
        //@ set map = \map_update(map, entries[index].key, value);
        return result;
    }

    Object putNotInDomain(Object key, Object value) {
        MapEntry[] newEntries = putExtendArray(key, value);
        entries = newEntries;
        //@ set footprint = \set_union(\dl_allElementsOfArray(entries, \all_fields(entries[0])), \set_union(\all_fields(this), \all_fields(entries)));
        //@ set map = \map_update(map, key, value);
        return null;
    }
    
    public Object remove(Object key) {
        int index = getIndexOfKey(key);
        if (index == -1) {
            return null;
        } else {
            return removeInDomain(index);
        }
    }
    
    void removeCopyOldEntries(MapEntry[] newEntries, int index) {
        copyMapEntries(newEntries, 0, 0, index);
        copyMapEntries(newEntries, index, index + 1, newEntries.length - index);
    }

    public MapEntry[] removeGetNewArray(int index) {
        MapEntry[] newEntries = newMapEntryArray(entries.length - 1);
        removeCopyOldEntries(newEntries, index);
        return newEntries;
    }

    Object removeInDomain(int index) {
        Object ret = entries[index].value;
        removeInDomainWithoutResult(index);
        return ret;
    }
    
    void removeInDomainWithoutResult(int index) {
        removeSetEnries(removeGetNewArray(index), index);
    }    
    
    public void removeSetEnries(MapEntry[] newEntries, int index){
        //@ set map = \map_remove(map, entries[index].key);
        entries = newEntries;
        //@ set footprint = \set_union(\dl_allElementsOfArray(entries, \all_fields(entries[0])), \set_union(\all_fields(this), \all_fields(entries)));
    }
    
    public int size() {
        return entries.length;
    }

}
