package gc;

public interface GCMonitor {

	void freeObject(int ref);
	
	void addStaticRoot(int ref);

	int getFreeedObjects();

	void reset();

	void addStackRoot(int ref);

	void visitChild(int parent, int child);
	
}
