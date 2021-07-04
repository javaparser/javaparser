package reflect;

import icecaptools.IcecapCompileMe;

public class Unboxing {

	@IcecapCompileMe
	public static void unbox(Object box) {
		if (box instanceof Long) {
			Long l = (Long) box;
			reportLong(l.longValue());
		} else if (box instanceof Integer) {
			Integer i = (Integer) box;
			reportInt(i.intValue());
		} else if (box instanceof Short) {
			Short s = (Short) box;
			reportShort(s.shortValue());
		} else if (box instanceof Byte) {
			Byte b = (Byte) box;
			reportByte(b.byteValue());
		} else if (box instanceof Boolean) {
			Boolean b = (Boolean) box;
			reportBoolean(b.booleanValue());
		} else if (box instanceof Character) {
			Character b = (Character) box;
			reportCharacter(b.charValue());
		}
	}
	
	@IcecapCompileMe
	public static Boolean boxBoolean(boolean b) {
		return new Boolean(b);
	}

	@IcecapCompileMe
	public static Byte boxByte(byte b) {
		return new Byte(b);
	}

	@IcecapCompileMe
	public static Short boxShort(short b) {
		return new Short(b);
	}

	@IcecapCompileMe
	public static Character boxCharacter(char b) {
		return new Character(b);
	}

	@IcecapCompileMe
	public static Integer boxInteger(int b) {
		return new Integer(b);
	}

	@IcecapCompileMe
	public static Long boxLong(long b) {
		return new Long(b);
	}

	private static native void reportLong(long l);

	private static native void reportInt(int i);

	private static native void reportShort(short s);

	private static native void reportByte(byte b);

	private static native void reportBoolean(boolean b);

	private static native void reportCharacter(char c);
}
