package vm;

public class Address32Bit extends Address {
	public int address;

	public Address32Bit(int address) {
		this.address = address;
	}

	@Override
	public void inc() {
		address++;
	}

	@Override
	public void add(int i) {
		address += i;
	}
	
	@Override
	public void sub(int offset) {
		address -= offset;
	}

	@Override
	public boolean isNull() {
		return address == 0;
	}
}
