package javax.safetycritical;

public class InnerPrivateMemory extends ManagedMemory { // HSO: not public

	ManagedMemory prev;

	public InnerPrivateMemory(int size, int BackingStoreOfThisMemory, 
	  ManagedMemory backingStoreProvider, String label) {
		super(size, BackingStoreOfThisMemory, backingStoreProvider, label);
	}
}
