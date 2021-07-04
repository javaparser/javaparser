package javax.safetycritical;

public final class TestPortal {

	public static void ManagedMemory_allocateBackingStore(int totalBackingStore) {
		ManagedMemory.allocateBackingStore(totalBackingStore);
	}

	public static ManagedMemory ManagedMemory_allocateImmortalMemory(
			int immortalSize) {
		return new ManagedMemory.ImmortalMemory(immortalSize);
	}

	public static ManagedMemory ManagedMemory_getOuterMemory(ManagedMemory m) {
		return ManagedMemory.getOuterMemory(m);
	}
	
	public static void executeInAreaOf (ManagedMemory mem, Runnable logic) {
		mem.flag = true;
		mem.executeInArea(logic);
	}
}
