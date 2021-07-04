package devices;

public class X86Writer implements Writer {

	private static native void nwrite(byte[] bytes, int length);
	
	@Override
	public void write(byte[] bytes, short length) {
		nwrite(bytes, length);
	}
}
