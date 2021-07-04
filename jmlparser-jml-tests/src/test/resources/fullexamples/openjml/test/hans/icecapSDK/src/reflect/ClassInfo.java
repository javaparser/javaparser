package reflect;

import icecaptools.IcecapCVar;
import icecaptools.IcecapCompileMe;
import util.ReferenceIterator;
import vm.Address;
import vm.Address32Bit;
import vm.Machine;
import vm.HardwareObject;

public abstract class ClassInfo extends HardwareObject {

	public ClassInfo(Address address) {
		super(address);
	}

	@IcecapCVar
	private static short NUMBEROFCLASSES_var;

	@IcecapCVar
	private static byte SUPPORTGC_var;

	private static class CachedClassInfo {
		ClassInfo cInfo;
		StringBuffer name;
		short[] references;
	}

	private static CachedClassInfo[] clazzes;
	private static ObjectReferenceOffsetIterator iterator;
	private static ReferencesArray ra;
	private static ArrayOverlay ao;
	private static ArrayReferenceOffsetIterator aroi;

	public short superClass;
	public byte dimension;
	public byte hasLock;
	public short dobjectSize;
	public short pobjectSize;

	@IcecapCompileMe
	protected static boolean gCSupported() {
		return SUPPORTGC_var > 0;
	}

	@IcecapCompileMe
	public static ClassInfo getClassInfoFromArchitecture(short index) {
		switch (Machine.architecture) {
		case Machine.X86_64:
			return new ClassInfoX86_64(index);
		default:
			return new ClassInfoX86_32(index);
		}
	}

	@IcecapCompileMe
	private static CachedClassInfo getCachedClassInfo(short index) {
		if (clazzes != null) {
			CachedClassInfo ccInfo = clazzes[index];
			if (ccInfo != null) {
				return ccInfo;
			} else {
				ccInfo = new CachedClassInfo();
				ccInfo.cInfo = getClassInfoFromArchitecture(index);
				clazzes[index] = ccInfo;
			}
		} else {
			clazzes = new CachedClassInfo[NUMBEROFCLASSES_var];
			iterator = new ObjectReferenceOffsetIterator();
			ra = new ReferencesArray();
			ao = new ArrayOverlay();
			aroi = new ArrayReferenceOffsetIterator();
		}
		return getCachedClassInfo(index);
	}

	public static ClassInfo getClassInfo(short index) {
		CachedClassInfo ccInfo = getCachedClassInfo(index);
		return ccInfo.cInfo;
	}

	@IcecapCompileMe
	public static short getNumberOfClasses() {
		return NUMBEROFCLASSES_var;
	}

	public StringBuffer getName() {
		short index = getIndex();
		CachedClassInfo ccInfo = clazzes[index];
		StringBuffer buffer = ccInfo.name;
		if (buffer != null) {
			return buffer;
		} else {
			buffer = new StringBuffer();
			CString cstring = new CString(getNameRef());

			while (cstring.hasNext()) {
				buffer.append(cstring.next());
			}
			ccInfo.name = buffer;
			return buffer;
		}
	}

	protected abstract short getIndex();

	protected abstract Address getNameRef();

	private static class ObjectReferenceOffsetIterator implements
			ReferenceIterator {
		private short[] offsets;
		private short top;

		public ObjectReferenceOffsetIterator() {
		}

		@Override
		public boolean hasNext() {
			return top < offsets.length;
		}

		@Override
		public int next() {
			int ref = offsets[top];
			top++;
			return ref;
		}

		public void setOffsets(short[] offsets) {
			this.offsets = offsets;
			top = 0;
		}
	}

	private static class ArrayReferenceOffsetIterator implements
			ReferenceIterator {
		private short offset;
		private short length;

		public ArrayReferenceOffsetIterator() {
		}

		@Override
		public boolean hasNext() {
			return length > 0;
		}

		@Override
		public int next() {
			int next = offset;
			offset += 4;
			length--;
			return next;
		}

		public void reset(short length) {
			this.length = length;
			this.offset = 2;
		}
	}

	private static class ArrayOverlay extends HeapAccessor {
		@SuppressWarnings("unused")
		public short classid;
		public short length;

		public ArrayOverlay() {
			super(0);
		}

		public void setAddress(int ref) {
			((Address32Bit)address).address = ref;
		}
	}

	public ReferenceIterator getReferenceOffsets(int ref) {
		short index = getIndex();
		CachedClassInfo ccInfo = clazzes[index];
		short[] references = ccInfo.references;
		if (references != null) {

			return newObjectReferenceOffsetIterator(references);
		} else {
			if (gCSupported()) {
				Address r = getReferencesRef();
				if (!r.isNull()) {
					return getReferenceIterator(ccInfo, r);
				} else if (this.dimension == 1) // this is a 1 dimensional array
				{
					if (this.dobjectSize > 0) // of component type
					{
						ao.setAddress(ref);
						short length = ao.length;
						aroi.reset(length);
						return aroi;
					}
				}
			}
			return null;
		}
	}

	private ReferenceIterator getReferenceIterator(CachedClassInfo ccInfo,
			Address r) {
		short[] references;
		ra.setAddress(r);
		byte shortReferences;
		byte byteReferences;
		byte top = 0;
		shortReferences = ra.getShortReferences();
		byteReferences = ra.getByteReferences();
		references = new short[shortReferences + byteReferences];

		for (byte i = 0; i < shortReferences; i++) {
			references[top++] = ra.nextShort();
		}

		for (byte i = 0; i < byteReferences; i++) {
			short s = ra.nextShort();
			references[top++] = (short) (s & 0xff);
			i++;
			if (i < byteReferences) {
				references[top++] = (short) (s >> 8);
			}
		}
		ccInfo.references = references;
		return newObjectReferenceOffsetIterator(references);
	}

	protected abstract Address getReferencesRef();

	private ReferenceIterator newObjectReferenceOffsetIterator(short[] offsets) {
		iterator.setOffsets(offsets);
		return iterator;
	}

	public abstract Address getInterfacesRef();
}
