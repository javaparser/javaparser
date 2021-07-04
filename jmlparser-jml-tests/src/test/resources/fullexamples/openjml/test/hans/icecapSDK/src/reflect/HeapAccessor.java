package reflect;

import vm.Address32Bit;
import vm.HardwareObject;

public class HeapAccessor extends HardwareObject {

	public HeapAccessor(int address) {
		super(new Address32Bit(address));
	}

}
