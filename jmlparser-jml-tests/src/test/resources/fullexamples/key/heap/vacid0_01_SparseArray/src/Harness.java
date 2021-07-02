public class Harness {
    
    static /*@ nullable @*/ SparseArray a, b;
    
    
    /*@ normal_behaviour
      @   ensures a.get(5) == 0 && b.get(7) == 0;
      @*/
    static void sparseArrayTestHarness1() {
	a = new SparseArray(10);
	b = new SparseArray(20);
    }
    
    
    /*@ normal_behaviour
      @   ensures a.get(5) == 1 && b.get(7) == 2;
      @   ensures a.get(0) == 0 && b.get(0) == 0;      
      @*/
    static void sparseArrayTestHarness2() {
	a = new SparseArray(10);
	b = new SparseArray(20);
	
	a.set(5, 1);
	b.set(7, 2);
    }
}
