package reflect;

import java.lang.reflect.Method;

public class ReflectionUtils {

	private static Method[] methodCache;

	public static Method getMethod(Class<?> cl, String name,
			Class<?>... parameterTypes) {

		short index = getMethodIndex(cl, name, parameterTypes);

		short numberOfMethods = MethodInfo.getNumberOfMethods();

		if (index != -1) {
			try {
				Method m = getCachedMethod(index, numberOfMethods);

				if (m == null) {
					m = Method.class.newInstance();
					writeMethodIndex(m, index);
					setMethodCache(m, index);
				}
				return m;
			} catch (InstantiationException e) {
			} catch (IllegalAccessException e) {
			}
			return null;
		}
		return null;
	}

	public static short getMethodIndex(Class<?> cl, String name,
			Class<?>... parameterTypes) {
		short numberOfMethods = MethodInfo.getNumberOfMethods();

		while (true) {
			String className = cl.getName();
			for (short index = 0; index < numberOfMethods; index++) {
				MethodInfo mInfo = MethodInfo.getMethodInfo(index);
				String currentName = mInfo.getName(index);
				if (currentName.startsWith(className)
						&& currentName.endsWith(name)) {

					if (currentName.length() == className.length()
							+ name.length() + 1) {
						if (mInfo.numArgs == parameterTypes.length) {
							return index;
						}
					}
				}
			}
			cl = cl.getSuperclass();
			if (cl == Object.class) {
				return -1;
			}
		}
	}

	private static class MethodObjectInfo extends ObjectInfo {
		private short shortValue;

		public short getShort(short offset) {
			short s;
			address.add((offset * 2) - 4);
			s = shortValue;
			address.sub((offset * 2) - 4);
			return s;
		}

		public void setShort(short offset, short value) {
			address.add((offset * 2) - 4);
			shortValue = value;
			address.sub((offset * 2) - 4);
		}
	}

	static MethodObjectInfo objectInfo;

	private static void writeMethodIndex(Method m, short index) {
		if (objectInfo == null) {
			objectInfo = new MethodObjectInfo();
		}
		objectInfo.setAddress(ObjectInfo.getAddress(m));
		objectInfo.setShort((short) 0, index);
	}

	public static short readMethodIndex(Method m) {
		if (objectInfo == null) {
			objectInfo = new MethodObjectInfo();
		}
		objectInfo.setAddress(ObjectInfo.getAddress(m));
		return objectInfo.getShort((short) 0);
	}

	private static void setMethodCache(Method m, short index) {
		methodCache[index] = m;
	}

	private static Method getCachedMethod(short index, short numberOfMethods) {
		if (methodCache == null) {
			methodCache = new Method[numberOfMethods];
		}
		return methodCache[index];
	}
}
