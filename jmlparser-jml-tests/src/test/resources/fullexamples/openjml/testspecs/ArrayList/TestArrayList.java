import java.util.ArrayList;

public class TestArrayList {
	
	@org.jmlspecs.annotation.SkipEsc
	public static void main(String... args) {
		esc(10);
	}
	
	public static void esc(int i) {
	ArrayList<Integer> a = new ArrayList<Integer>();
	boolean b1 = a.isEmpty();
	//@ assert b1;
	int i1 = a.size();
	//@ assert i1 == 0;
	b1 = a.add(1);
	//@ assert b1;
	//@ assert a.size() == 1;
	//@ assert !a.isEmpty();
	a.add(1,2);
	//@ assert a.get(1) == 2;
	//@ assert a.size() == 2;
	b1 = a.contains(2);
	//@ assert b1;
	b1 = a.contains(3);
	//@ assert !b1;
	a.set(1,3);
	//@ assert a.size() == 2;
	//@ assert a.get(1) == 3;
	b1 = a.contains(3);
	//@ assert b1;
	b1 = a.contains(2);
	//@ assert !b1;
	i1 = a.get(0);
	//@ assert i1 == 1;
	i1 = a.indexOf(3);
	//@ assert i1 == 1;
	i1 = a.lastIndexOf(1);
	//@ assert i1 == 0;
	i1 = a.remove(1);
	//@ assert i1 == 3;
	//@ assert a.size() == 1;
	
	ArrayList<Integer> aa = (ArrayList<Integer>)a.clone();
	
	
	
	
	a.clear();
	b1 = a.isEmpty();
	//@ assert b1;
	
	// Still to check:
	// addAll, addAll, clone, ensuresCapacity, trimToSize, removeRange, toArray
	// AbstractList: iterator, listIterator, subList, equals, hashCode
	// AbstractCollection: toArray(2 version), containsAll, removeAll, retainAll, toString

	// anything inherited from  Iterable, RandomAccess, Cloneable, Serializable, 
}

}