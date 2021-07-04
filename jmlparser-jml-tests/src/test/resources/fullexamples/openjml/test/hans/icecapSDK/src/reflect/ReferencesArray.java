package reflect;

import vm.Address;
import vm.Address32Bit;
import vm.HardwareObject;
import icecaptools.IcecapCompileMe;

public class ReferencesArray extends HardwareObject {
	private short value;

	@IcecapCompileMe
	public ReferencesArray(int address) {
		super(new Address32Bit(address));
	}

	public ReferencesArray() {
		super(new Address32Bit(0));
	}

	@IcecapCompileMe
	public byte getShortReferences() {
		return (byte) (value >> 8);
	}

	@IcecapCompileMe
	public byte getByteReferences() {
		return (byte) (value & 0xff);
	}

	public short nextShort() {
		address.add(2);
		return value;
	}

	public void setAddress(Address address) {
		super.address = address;
	}
}
