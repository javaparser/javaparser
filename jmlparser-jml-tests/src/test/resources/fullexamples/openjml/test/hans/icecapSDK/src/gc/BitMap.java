package gc;

import util.ReferenceIterator;
import util.ReferenceList;

public class BitMap {

	public static final byte WHITE = 3;
	public static final byte GREY = 1;
	public static final byte BLACK = 2;
	public static final byte HATCHED = 0;

	private int blockSize;
	// In int/words

	private int startAdr;
	// In int/words

	private int heapSize;
	// In int/words

	private int bitMapSize; 
	
	private byte[] bitMap;

	public BitMap(int blockSize, int startAdr, int heapSize) {
		this.blockSize = blockSize;
		this.startAdr = startAdr;
		if (heapSize > 64000)
		{
			heapSize = 64000;
		}
		this.heapSize = heapSize;
		bitMapSize = ((heapSize / blockSize) / 4) + 1;
		bitMap = new byte[bitMapSize];
	}

	public void clear() {
		for (int i = 0; i < bitMap.length; i++) {
			bitMap[i] = 0;
		}
	}

	public boolean isRefWhite(int ref) {
		int index = getIndex(ref);
		int offSet = getOffset(ref);
		if (((bitMap[index] & (1 << (offSet << 1))) != 0) && ((bitMap[index] & (1 << ((offSet << 1) + 1))) != 0)) {
			return true;
		}
		return false;
	}

	public boolean isRefGrey(int ref) {
		int index = getIndex(ref);
		int offSet = getOffset(ref);

		if (((bitMap[index] & (1 << (offSet << 1))) != 0) && ((bitMap[index] & (1 << ((offSet << 1) + 1))) == 0)) {
			return true;
		}
		return false;
	}

	public boolean isRefBlack(int ref) {
		int index = getIndex(ref);
		int offSet = getOffset(ref);

		if (((bitMap[index] & (1 << (offSet << 1))) == 0) && ((bitMap[index] & (1 << ((offSet << 1) + 1))) != 0)) {
			return true;
		}
		return false;
	}

	public boolean isRefHatched(int ref) {
		int index = getIndex(ref);
		int offSet = getOffset(ref);

		if (((bitMap[index] & (1 << (offSet << 1))) == 0) && ((bitMap[index] & (1 << ((offSet << 1) + 1))) == 0)) {
			return true;
		}
		return false;
	}

	public void shadeRefGrey(int ref) {
		int index = getIndex(ref);
		int offSet = getOffset(ref);

		bitMap[index] = (byte) (bitMap[index] | (1 << (offSet << 1)));
		bitMap[index] = (byte) (bitMap[index] & ~(1 << ((offSet << 1) + 1)));
	}

	private int getOffset(int ref) {
		return ((ref - startAdr) / blockSize) & 0x3;
	}

	private int getIndex(int ref) {
		return ((ref - startAdr) / blockSize) >> 2;
	}

	public void shadeRefWhite(int ref) {
		int index = getIndex(ref);
		int offSet = getOffset(ref);

		bitMap[index] = (byte) (bitMap[index] | (1 << (offSet << 1)));
		bitMap[index] = (byte) (bitMap[index] | (1 << ((offSet << 1) + 1)));
	}

	public void shadeRefBlack(int ref) {
		int index = getIndex(ref);
		int offSet = getOffset(ref);

		bitMap[index] = (byte) (bitMap[index] & (~(1 << (offSet << 1))));
		bitMap[index] = (byte) (bitMap[index] | (1 << ((offSet << 1) + 1)));
	}

	public ReferenceIterator getFreeList() {
		ReferenceList freeList = new ReferenceList();
		int i = 0;
		while (i < bitMap.length) {
			byte nextByte = bitMap[i];
			if (nextByte != 0) {
				int ref = ((i << 2) * blockSize) + startAdr;
				for (int j = 0; j < 4; j++) {
					if (isRefWhite(ref))
					{
						freeList.add(ref);
						shadeRefHatched(ref);
					}
					else if (isRefBlack(ref))
					{
						shadeRefWhite(ref);
					}
					ref += blockSize;
				}
			}
			i++;
		}
		return freeList.iterator();
	}

	private void shadeRefHatched(int ref) {
		int index = getIndex(ref);
		int offSet = getOffset(ref);

		bitMap[index] = (byte) (bitMap[index] & ~(1 << (offSet << 1)));
		bitMap[index] = (byte) (bitMap[index] & ~(1 << ((offSet << 1) + 1)));

	}

	public boolean isWithinRangeOfHeap(int possibleRef) {
		return (possibleRef >= startAdr) && (possibleRef < startAdr + heapSize);
	}

	public int getSize() {
		return this.bitMapSize;
	}
}
