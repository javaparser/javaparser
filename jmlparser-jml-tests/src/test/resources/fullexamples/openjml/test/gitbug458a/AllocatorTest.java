
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

		byte[] b4 = Allocator.alloc(10);
		//@ assert b4 != null;
		//@ assert b4.length == 10;
		//@ assert b1 != b4;
		//@ assert b2 != b4;
		//@ assert b3 != b4;
		
		byte[] b5 = Allocator.alloc(10);
		//@ assert b5 != null;
		//@ assert b5.length == 10;
		//@ assert b1 != b5;
		//@ assert b2 != b5;
		//@ assert b3 != b5;
		//@ assert b4 != b5;
		
		byte[] b6 = Allocator.alloc(10);
		//@ assert b6 != null;
		//@ assert b6.length == 10;
		//@ assert b1 != b6;
		//@ assert b2 != b6;
		//@ assert b3 != b6;
		//@ assert b4 != b6;
		//@ assert b5 != b6;
		
		byte[] b7 = Allocator.alloc(10);
		//@ assert b7 != null;
		//@ assert b7.length == 10;
		//@ assert b1 != b7;
		//@ assert b2 != b7;
		//@ assert b3 != b7;
		//@ assert b4 != b7;
		//@ assert b5 != b7;
		//@ assert b6 != b7;

		byte[] b8 = Allocator.alloc(10);
		//@ assert b8 != null;
		//@ assert b8.length == 10;
		//@ assert b1 != b8;
		//@ assert b2 != b8;
		//@ assert b3 != b8;
		//@ assert b4 != b8;
		//@ assert b5 != b8;
		//@ assert b6 != b8;
		//@ assert b7 != b8;
		
		byte[] b9 = Allocator.alloc(10);
		//@ assert b9 != null;
		//@ assert b9.length == 10;
		//@ assert b1 != b9;
		//@ assert b2 != b9;
		//@ assert b3 != b9;
		//@ assert b4 != b9;
		//@ assert b5 != b9;
		//@ assert b6 != b9;
		//@ assert b7 != b9;
		//@ assert b8 != b9;

		byte[] b10 = Allocator.alloc(10);
		//@ assert b10 != b1;
	}
}
