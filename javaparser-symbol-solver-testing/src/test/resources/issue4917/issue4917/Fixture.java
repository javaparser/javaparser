package issue4917;

import java.util.Collections;
import java.util.List;
import java.util.stream.Stream;

/** Minimal source-only stand-ins for the grid, query, paging and service APIs in issue 4917. */
public class Fixture {

    public static class Query<T> {}

    public static class PageRequest<T> {}

    public static class Task {
        public boolean matches(PageRequest<Task> request) {
            return true;
        }
    }

    public interface FetchCallback<T> {
        Stream<T> fetch(Query<T> query);
    }

    public static class Grid<T> {
        public void setItems(FetchCallback<T> callback) {}
    }

    public static class TaskService {
        public List<Task> list(PageRequest<Task> request) {
            return Collections.emptyList();
        }
    }

    public static class Helpers {
        public static PageRequest<Task> toSpringPageRequest(Query<Task> query) {
            return new PageRequest<>();
        }
    }

    public static class OverloadedHelpers {
        public static PageRequest<Task> toSpringPageRequest(Object query) {
            return new PageRequest<>();
        }

        public static PageRequest<Task> toSpringPageRequest(String query) {
            return new PageRequest<>();
        }

        public static PageRequest<Task> toSpringPageRequest(Query<Task> query) {
            return new PageRequest<>();
        }
    }

    public static class GenericHelpers {
        public static <T> PageRequest<T> toSpringPageRequest(Query<T> query) {
            return new PageRequest<>();
        }
    }

    public static class StringHelpers {
        public static PageRequest<Task> toSpringPageRequest(String query) {
            return new PageRequest<>();
        }
    }

    public static class DuplicateHelpers {
        public static PageRequest<Task> toSpringPageRequest(Query<Task> query) {
            return new PageRequest<>();
        }
    }

    public static class ObjectHelpers {
        public static PageRequest<Task> toSpringPageRequest(Object query) {
            return new PageRequest<>();
        }
    }

    public static class InheritedHelpers extends Helpers {}

    public static class HidingHelpers extends Helpers {
        public static PageRequest<Task> toSpringPageRequest(Query<Task> query) {
            return new PageRequest<>();
        }
    }
}
