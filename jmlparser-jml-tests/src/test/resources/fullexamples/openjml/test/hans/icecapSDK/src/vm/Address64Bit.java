package vm;

public class Address64Bit extends Address {
	public long address;
	
	public Address64Bit(long address) {
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
	public boolean isNull() {
		return address == 0;
	}

	@Override
	public void sub(int offset) {
		address -= offset;
	}
}
