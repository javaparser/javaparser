package reflect;

import icecaptools.IcecapCVar;
import icecaptools.IcecapCompileMe;
import vm.Address;
import vm.Machine;
import vm.HardwareObject;

public abstract class MethodInfo extends HardwareObject {
	public short classIndex;
	public short maxStack;
	public short maxLocals;
	public short codeSize;
	public byte numExceptionHandlers;
	public byte numArgs;
	public byte minfo;

	@IcecapCVar(expression = "NUMBEROFMETHODS", requiredIncludes = "")
	private static short NUMBEROFMETHODS_var;

	private static String[] names;
	private static MethodInfo[] infos;

	public MethodInfo(Address address) {
		super(address);
	}

	@IcecapCompileMe
	public static short getNumberOfMethods() {
		return NUMBEROFMETHODS_var;
	}

	protected abstract Address getNameRef();

	@IcecapCompileMe
	public static MethodInfo getMethodInfo(short index) {
		MethodInfo mi = getCachedInfo(index);
		if (mi == null) {
			switch (Machine.architecture) {
			case Machine.X86_64:
				mi = new MethodInfoX86_64(index);
				break;
			default:
				mi = new MethodInfoX86_32(index);
			}
			setCachedInfo(mi, index);
		}
		return mi;
	}

	private static void setCachedInfo(MethodInfo mi, short index) {
		if (infos == null) {
			infos = new MethodInfo[getNumberOfMethods()];
		}
		infos[index] = mi;
	}

	private static MethodInfo getCachedInfo(short index) {
		if (infos == null) {
			return null;
		} else {
			return infos[index];
		}
	}

	public String getName(short index) {
		String name = getCachedName(index);

		if (name == null) {
			StringBuffer buffer = new StringBuffer();
			CString cstring = new CString(getNameRef());

			while (cstring.hasNext()) {
				buffer.append(cstring.next());
			}
			name = buffer.toString();
			setCachedName(name, index);
		}
		return name;
	}

	private void setCachedName(String name, short index) {
		if (names == null) {
			names = new String[getNumberOfMethods()];
		}
		names[index] = name;
	}

	private String getCachedName(short index) {
		if (names == null) {
			return null;
		} else {
			return names[index];
		}
	}
}
