package reflect;

import vm.Address32Bit;


public class ObjectInfo extends HeapAccessor {

	public short classId;
	private int value;
	
	public ObjectInfo(Object oi) {
		super(getAddress(oi));
	}

	public ObjectInfo(int address) {
		super(address);
	}
	
	public ObjectInfo() {
		super(0);
	}

	public static native int getAddress(Object oi);

	public int getRef(short offset) {
		int ref;
		address.add(offset);
		ref = value;
		address.sub(offset);
		return ref;
	}

	public void setAddress(int ref) {
		((Address32Bit)address).address = ref;
	}
}
