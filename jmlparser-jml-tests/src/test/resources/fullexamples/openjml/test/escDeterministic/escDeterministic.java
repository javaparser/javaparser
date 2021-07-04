
//@ immutable
public class escDeterministic {

	//@ ensures true;
	//@ function 
	static public int comp(int a) { return 0; }

	public int a;
	public int b;
	public int c;
	
	//@ ensures a == b;
	public void m() {
		a = comp(10);
		c = 20;
		b = comp(10);
		//@ assert a == b;
	}

	//@ ensures true;
	//@ function 
	abstract public int acomp(int a);

	//@ assignable \everything;
	//@ ensures acomp(10) == acomp(10);
	public void n() {}

}
