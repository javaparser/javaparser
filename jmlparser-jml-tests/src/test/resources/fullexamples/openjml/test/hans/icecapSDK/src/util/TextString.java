package util;

public class TextString implements Compareable {

	private byte top;
	private char[] characters;

	public TextString(byte initialCapacity) {
		characters = new char[initialCapacity];
		top = 0;
	}

	public void add(char ascii) {
		if (top < characters.length) {
			characters[top++] = ascii;
		}
	}

	@Override
	public String toString() {
		return new String(characters);
	}

	@Override
	public byte compareTo(Compareable right) {
		TextString other = (TextString) right;
		byte index = 0;
		while ((index < top) && (index < other.top)) {
			char thisc, otherc;
			thisc = characters[index];
			otherc = other.characters[index];
			if (thisc < otherc) {
				return -1;
			} else if (thisc > otherc) {
				return 1;
			}
			index++;
		}

		if (top < other.top) {
			return -1;
		} else if (top > other.top) {
			return 1;
		}
		return 0;
	}
}
