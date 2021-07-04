package reflect;

import vm.Address;
import vm.HardwareObject;


class CString extends HardwareObject {
	private byte b;
	
	public CString(Address address) {
		super(address);
	}

	public boolean hasNext() {
		return (b != 0);
	}

	public char next() {
		char next = (char)b;
		address.inc();
		return next;
	}
}
