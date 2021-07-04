package reflect;

import icecaptools.IcecapCompileMe;
import vm.Address;
import vm.Address32Bit;
import vm.Address64Bit;
import vm.Machine;
import vm.HardwareObject;

public class StaticRefInfo {

	private static class OffsetsArray extends HardwareObject {
		public int data;

		public OffsetsArray(int address) {
			super(new Address32Bit(address));
		}

		public OffsetsArray(long address) {
			super(new Address64Bit(address));
		}

		public void advance() {
			address.add(4);
		}
	}

	private static int[] offsets;

	@IcecapCompileMe
	public static int[] getOffsets() {
		if (offsets == null) {
			OffsetsArray oa;
			switch (Machine.architecture) {
			case Machine.X86_64:
				oa = new OffsetsArray(StaticRefInfo64.staticReferenceOffsets);
				break;
			case Machine.X86_32:
				oa = new OffsetsArray(StaticRefInfo32.staticReferenceOffsets);
				break;
			default:
				oa = null;
				break;
			}
			int length = oa.data;
			short index = 0;
			offsets = new int[length];
			oa.advance();
			while (length > 0) {
				offsets[index++] = oa.data;
				oa.advance();
				length--;
			}
		}
		return offsets;
	}

	private static class ReferenceArray extends HardwareObject {
		public int data;

		public ReferenceArray() {
			super(new Address32Bit(0));
		}

		public void setAddress(Address adr) {
			this.address = adr;
		}
	}

	static ReferenceArray ra;

	@IcecapCompileMe
	public static int getReference(int offset) {

		if (ra == null) {
			ra = new ReferenceArray();
		}
		
		Address adr;
		
		switch (Machine.architecture) {
		case Machine.X86_64:
			adr = new Address64Bit(StaticRefInfo64.classData);
			break;
		case Machine.X86_32:
			adr = new Address64Bit(StaticRefInfo32.classData);
			break;
		default:
			adr = null;
			break;
		}
		adr.add(offset);
		ra.setAddress(adr);

		return ra.data;
	}
}
