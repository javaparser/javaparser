
public class Magic {
	public static void main(String[] args) {
		System.out.println(magic());
	}
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public static long magic() {
		return System.currentTimeMillis()*0;
	}
}
