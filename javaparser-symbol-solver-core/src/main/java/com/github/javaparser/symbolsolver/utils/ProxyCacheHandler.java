package com.github.javaparser.symbolsolver.utils;

import java.lang.reflect.InvocationHandler;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.List;
import java.util.WeakHashMap;
import java.util.stream.Collectors;

import com.github.javaparser.utils.Utils;
import com.google.common.base.Objects;

/*
 *  Proxy with an internal cache
 */
public class ProxyCacheHandler<T> implements InvocationHandler {

    // cache to tweak performance issue (key is composed from method and args)
    private static ThreadLocal<Cache> localCache = ThreadLocal.withInitial(() -> new Cache());

    private Object target;

    private List<Method> cacheableMethods;

    public ProxyCacheHandler(Object target) {
        this.target = Utils.assertNotNull(target);
        this.cacheableMethods = getCacheableMethods();
    }

    @Override
    public Object invoke(Object proxy, Method method, Object[] args) throws Throwable {
        Object ref = null;
        if (isCached(method)) {
            Args key = new Args(target, method, args);
            System.out.println("calling cache with key " + key.toString());
            ref = get(key);
            if (ref == null) {
                try {
                    // invoke real method and put result in local cache
                    ref = method.invoke(target, args);
                    put(key, ref);
                } catch (InvocationTargetException e) {
                    throw e.getTargetException();
                }
            }
        } else {
            try {
                // invoke real method
                ref = method.invoke(target, args);
            } catch (InvocationTargetException e) {
                throw e.getTargetException();
            }
        }
        return ref;
    }
    
    /*
     * Clear the internal cache
     */
    public static void clearCache() {
        localCache.get().clear();
    }

    /*
     * get object from cache
     */
    private Object get(Args key) {
        return localCache.get().get(key);
    }

    /*
     * put non null object in cache
     */
    private void put(Args key, Object value) {
        if (value == null || key == null) {
            return;
        }
        if (localCache.get().contains(key)) {
//            System.out.println("Trying to put a value in cache that is already cached with key " + key);
            return;
        }
//        System.out.println("putting value in cache " + value.toString() + " with key " + key);
        localCache.get().put(key, value);
    }

    /*
     * return true if the called method is cacheable
     */
    private boolean isCached(Method method) {
        return cacheableMethods.stream().anyMatch(m -> {
            return m.getName().equals(method.getName())
                    && Arrays.equals(m.getParameterTypes(), method.getParameterTypes());
        });
    }

    /*
     * return all method that define a Cacheable annotation
     */
    private List<Method> getCacheableMethods() {
        return Arrays.stream(target.getClass().getMethods()).filter(m -> isCacheable(m)).collect(Collectors.toList());
    }

    /*
     * return true if the method has a Cacheable annotations
     */
    private boolean isCacheable(Method method) {
        return method.isAnnotationPresent(Cacheable.class);
    }

    private static class Cache {
        private WeakHashMap<Args, Object> cache = new WeakHashMap<>();

        public void clear() {
            cache = new WeakHashMap<>();
        }
        
        public boolean contains(Args args) {
            return cache.containsKey(args);
        }

        public Object get(Args args) {
            return cache.get(args);
        }

        public void put(Args args, Object value) {
            cache.put(args, value);
        }
    }

    private static final class Args {
        private final Object mTarget;
        private final Method mMethod;
        private final Object[] mArgs;
        private final int mHash;

        public Args(Object target, final Method m, final Object[] args) {
            mTarget = target;
            mMethod = m;
            mArgs = args;
            // precalculate hash
            mHash = calcHash();
        }

        public String toString() {
            StringBuffer sb = new StringBuffer().append("target=").append(mTarget.toString())
                    .append(", method=").append(mMethod.toString())
                    .append("[");
            for (Object arg : mArgs) {
                sb.append(arg.toString()).append(",");
            }
            sb.append("]");
            return sb.toString();
        }

        /**
         * Method and all the arguments have to be equal. Assumes that obj is of
         * the same type.
         */
        @Override
        public boolean equals(final Object obj) {
            final Args other = (Args) obj;
            if (!mTarget.equals(other.mTarget)) {
                return false;
            }
            if (!mMethod.equals(other.mMethod)) {
                return false;
            }
            for (int i = 0; i < mArgs.length; ++i) {
                Object o1 = mArgs[i];
                Object o2 = other.mArgs[i];
                if (!(o1 == null ? o2 == null : o1.equals(o2))) {
                    return false;
                }
            }
            return true;
        }

        /**
         * Use the precalculated hash.
         */
        @Override
        public int hashCode() {
            return mHash;
        }

        /**
         * Try to use a good & fast hash function here.
         */
        public int calcHash() {
            int h = Objects.hashCode(mTarget, mMethod);
            for (final Object o : mArgs) {
                h = h * 65599 + (o == null ? 0 : o.hashCode());
            }
            return h;
        }
    }

}
