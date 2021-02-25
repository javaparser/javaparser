package com.github.javaparser.jml;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

/**
 * This class handles the management of services and implementations.
 * <p>
 * This class is a flexible alternative for a mediator. You can register and deregister implementation for services.
 * And also you can lookup them up. Multiple implementations are possible; also notification on service change.
 * <p>
 * {@link Lookup} can be arranged hierarchical, incl. support for notification.
 *
 * @author Alexander Weigl
 * @version 1 (15.03.19)
 */
public class Lookup {
    /**
     * Registered services. The first service in the list is the default.
     */
    private final HashMap<Class<?>, LinkedList<?>> serviceMap = new HashMap<>();

    public Lookup() {
    }

    public Lookup(Lookup defaultServices) {
        defaultServices.serviceMap.forEach((a, b) -> serviceMap.put(a, new LinkedList<>(b)));
    }

    /**
     * Get all registered implementations for the given service class.
     *
     * @param service
     * @param <T>
     * @return
     */
    public <T> Collection<T> lookupAll(Class<T> service) {
        return getList(service);
    }

    /**
     * Get the current default implementation of the given service.
     *
     * @param service
     * @param <T>
     * @return
     */
    public <T> T get(Class<T> service) {
        List<? extends T> t = getList(service);
        if (t.isEmpty()) {
            throw new IllegalStateException("Service $service not registered");
        } else {
            return t.get(0);
        }
    }

    /**
     * Register
     *
     * @param obj
     * @param service
     * @param <T>
     */
    public <T> void register(T obj, Class<T> service) {
        List<T> list = getList(service);
        list.add(0, obj);
    }

    public <T> void deregister(T obj, Class<T> service) {
        boolean b = getList(service).remove(obj);
    }

    @SuppressWarnings("unchecked")
    public <T> void register(T o) {
        register(o, (Class<T>) o.getClass());
    }

    @SuppressWarnings("unchecked")
    private <T> List<T> getList(Class<T> service) {
        return (List<T>) serviceMap.computeIfAbsent(service, (k -> new LinkedList<>()));
    }
}