public class StringSet {

    private /*@ spec_public nullable @*/ String[] elements;
    private /*@ spec_public @*/ int size;

    /*@ public instance invariant this.size > 0; @*/
    /*@ private instance invariant \typeof(elements) == \type(String[]); @*/

    /*@ public instance invariant
      @   this.elements != null && this.elements.length == this.size;
      @*/	
    public StringSet (int size) {
	assert (size > 0);
	this.size = size;
	elements = new String[size];
    }
	
    /*@ public normal_behavior
      @  requires s != null && s.hashCode() >= 0;
      @  requires this.elements[(s.hashCode() % this.size)] == null;
      @  assignable this.elements[(s.hashCode() % this.size)];
      @  ensures this.elements[(s.hashCode() % this.size)] == s;
      @  ensures \result == true;		
      @ also
      @ public normal_behavior
      @  requires s != null && s.hashCode() < 0;
      @  requires this.elements[(-(s.hashCode() + 1) % this.size)] == null;
      @  assignable this.elements[(-(s.hashCode() + 1) % this.size)];
      @  ensures this.elements[(-(s.hashCode() + 1) % this.size)] == s;
      @  ensures \result == true;     
      @ also		
      @ public normal_behavior
      @  requires s != null && s.hashCode() >= 0;
      @  requires this.elements[(s.hashCode() % this.size)] != null;
      @  assignable \nothing;
      @  ensures \result == elements[(s.hashCode() % this.size)].equals(s);		
      @ also
      @ public normal_behavior
      @  requires s != null && s.hashCode() < 0;
      @  requires this.elements[(-(s.hashCode() + 1) % this.size)] != null;
      @  assignable \nothing;
      @  ensures \result == this.elements[(-(s.hashCode() + 1) % this.size)].equals(s);      
      @ also		
      @ public normal_behavior
      @  requires s == null;
      @  assignable \nothing;
      @  ensures \result == false;
      @*/
    public boolean insert (String /*@ nullable @*/ s) {
	if (s==null) return false;
	int hash = s.hashCode();
	hash = hash < 0 ? -(hash + 1) : hash; 
	if (hash % size >= size) {
	    return false;
	} else {
	    if (elements[hash % size] == null) {
		elements[hash % size] = s;
		return true;
	    } else {
		return elements[hash % size].equals(s);
	    }
	}
    }
	
    /*@ public normal_behavior
      @  requires s != null && s.hashCode() >= 0;
      @  assignable \nothing;
      @  ensures \result == 
      @  s.equals(this.elements[s.hashCode() % this.size]);		
      @ also
      @ public normal_behavior
      @  requires s != null && s.hashCode() < 0;
      @  assignable \nothing;
      @  ensures \result == 
      @    s.equals(this.elements[-(s.hashCode() + 1) % this.size]);		
      @ also		
      @ public normal_behavior
      @  requires s == null;
      @  assignable \nothing;
      @  ensures \result == false;
      @*/
    public boolean contains (String /*@ nullable @*/ s) {
	if (s==null) return false;
	int hash = s.hashCode();
	hash = hash < 0 ? -(hash + 1) : hash; 
	if (hash % size >= size) {
	    return false;
	} else { 
	    return s.equals(elements[hash % size]);
	}
    }
		
}
