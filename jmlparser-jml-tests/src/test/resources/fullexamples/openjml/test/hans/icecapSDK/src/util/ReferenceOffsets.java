package util;

public class ReferenceOffsets {
	private short[] offsets;

	private short top;

	private short nextScanIndex;

	public ReferenceOffsets() {
		offsets = null;
	}

	public byte size() {
		return (byte) top;
	}

	public void insert(short i) throws Exception {
		if (i < 0) {
			throw new IllegalArgumentException();
		}

		if (top > 255) {
			throw new Exception("Too many references in object");
		}

		if (offsets == null) {
			offsets = new short[10];
		}

		if (top < offsets.length) {
			offsets[top++] = i;
		} else {
			extend();
			insert(i);
		}
	}

	private void extend() {
		short[] nbyteOffsets = new short[offsets.length * 2];
		for (byte i = 0; i < top; i++) {
			nbyteOffsets[i] = offsets[i];
		}
		offsets = nbyteOffsets;
	}

	public byte byteOffsetsSize() {
		short index = 0;
		byte sum = 0;
		while (index < top) {
			if (offsets[index] < 256) {
				sum++;
			}
			index++;
		}
		return sum;
	}

	public byte shortOffsetsSize() {
		return (byte) (top - byteOffsetsSize());
	}

	public void startScanByteOffsets() {
		nextScanIndex = 0;
	}

	public short getNextByteOffset() {
		short res;
		while (offsets[nextScanIndex] > 255) {
			nextScanIndex++;
		}
		res = offsets[nextScanIndex++];
		return res;
	}

	public void startScanShortOffsets() {
		startScanByteOffsets();
	}

	public short getNextShortOffset() {
		short res;
		while (offsets[nextScanIndex] <= 255) {
			nextScanIndex++;
		}
		res = offsets[nextScanIndex++];
		return res;
	}
}
