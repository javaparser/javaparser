package devices;

public class Console {

	private static final int DEFAULT_LENGTH = 512;  //256; //128; // HSO: June 2014
	private static byte[] bytes;

	static {
		bytes = new byte[DEFAULT_LENGTH + 1];
	}

	public static Writer writer;
	
	static
	{
		writer = new X86Writer();
	}

	public static void println(String string) {
		println(string, true);
	}

	private static void println(String string, boolean addNewLine) {
		short length = (short) string.length();
		if (addNewLine) {
			length++;
		}
		getBytes(string, addNewLine);
		writer.write(bytes, length);
	}

	private static byte[] getBytes(String string, boolean addNewLine) {
		int index = 0;
		int length = string.length();

		while ((index < length) && (index < DEFAULT_LENGTH - 1)) {
			bytes[index] = (byte) string.charAt(index);
			index++;
		}
		if (addNewLine) {
			bytes[index] = '\n';
		}
		return bytes;
	}

	public static void print(long l) {
		print("" + l);
	}

	public static void print(String space) {
		println(space, false);
	}

	public static void println(int i) {
		println("" + i);

	}

}
