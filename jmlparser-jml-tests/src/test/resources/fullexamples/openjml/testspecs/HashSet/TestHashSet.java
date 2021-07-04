import java.util.HashSet;

public class TestHashSet {
	
	@org.jmlspecs.annotation.SkipEsc
	public static void main(String... args) {
		esc(10);
	}
	
	public static void esc(int i) {
	HashSet<Integer> a = new HashSet<Integer>();
	boolean b1 = a.isEmpty();
	//@ assert b1;
	int i1 = a.size();
	//@ assert i1 == 0;
	b1 = a.add(1);
	//@ assert b1;
	//@ assert a.size() == 1;
	//@ assert !a.isEmpty();
/*	a.add(2);
	//@ assert a.size() == 2;
	b1 = a.contains(2);
	//@ assert b1;
/*	b1 = a.contains(3);
	//@ assert !b1;
	b1 = a.remove(1);
	//@ assert b1;
	//@ assert a.size() == 1;
	b1 = a.remove(10);
	//@ assert !b1;
	//@ assert a.size() == 1;
	
	HashSet<Integer> aa = (HashSet<Integer>)a.clone();
	
	
	
	
	a.clear();
	b1 = a.isEmpty();
*/	//@ assert b1;
	
	// Still to check:
	// HashSet: other constructors
	// Set: addAll, retainAll, removeAll, containsAll, equals, hashCode, toArray
	// AbstractCollection: toArray(2 version), containsAll, removeAll, retainAll, toString

	// anything inherited from Collection, Iterable,  Cloneable, Serializable, 
}

}