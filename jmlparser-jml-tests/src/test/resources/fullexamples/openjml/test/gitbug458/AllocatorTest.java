package alloc;

public class AllocatorTest {
	public void testAllocSmall() {
		byte[] b1 = Allocator.alloc(10);
		//@ assert b1 != null;
		//@ assert b1.length == 10;
		
		byte[] b2 = Allocator.alloc(10);
		//@ assert b2 != null;
		//@ assert b2.length == 10;
		//@ assert b1 != b2;
	}
	
	public void testAllocLarge() {
		byte[] b1 = Allocator.alloc(10);
		//@ assert b1 != null;
		//@ assert b1.length == 10;
		
		byte[] b2 = Allocator.alloc(10);
		//@ assert b2 != null;
		//@ assert b2.length == 10;
		//@ assert b2 != b1;
		
		byte[] b3 = Allocator.alloc(10);
		//@ assert b3 != null;
		//@ assert b3.length == 10;
		//@ assert b1 != b3;
		//@ assert b2 != b3;

	}
}
