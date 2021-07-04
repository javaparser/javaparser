public class S extends P {

	public int calc(int x) {
		return super.calc(x*10);
	}
	
	public static void main(String[] args) {
		S s = new S(); // doesn't matter if s is P or S
		System.out.println(s.calc(3));
	}
}
