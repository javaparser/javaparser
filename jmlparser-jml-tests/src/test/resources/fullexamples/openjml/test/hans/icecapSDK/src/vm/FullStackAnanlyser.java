package vm;

public class FullStackAnanlyser implements StackAnalyser {

	private int numberOfStacksCreated;

	static int[][] stacks;

	static {
		stacks = new int[10][];
	}

	@Override
	public void addStack(int[] stack) {
		if (stack != null) {
			if (numberOfStacksCreated < stacks.length) {
				for (short index = 0; index < stack.length; index++) {
					stack[index] = index;
				}
				stacks[numberOfStacksCreated++] = stack;
			}
		}
	}

	@Override
	public void reportStackUsage() {
		Memory.executeInTrackingArea(new Runnable() {

			@Override
			public void run() {
				devices.Console.println("Created " + numberOfStacksCreated + " stacks");
				for (byte index = 0; index < stacks.length; index++) {
					if (stacks[index] != null)
					{
						analyseStack(stacks[index]);
						devices.Console.println("stack " + index + "[" + best_start_of_unused_area + ", " + best_end_of_unused_area + "][" + stacks[index].length + "]");
					}
				}
			}
		});
	}

	private static final int USEDSTACKCELL = 10;
	private static final int UNUSEDSTACKCELL = 11;

	private int state;

	private int best_start_of_unused_area;
	private int best_end_of_unused_area;

	private void analyseStack(int[] stack) {
		state = USEDSTACKCELL;
		int index = 0;
		int start_of_unused_area = 0;
		int end_of_unused_area = 0;

		best_start_of_unused_area = 0;
		best_end_of_unused_area = 0;

		while (index < stack.length) {
			switch (state) {
			case USEDSTACKCELL:
				if (stack[index] == index) {
					start_of_unused_area = index;
					state = UNUSEDSTACKCELL;
				}
				break;
			case UNUSEDSTACKCELL:
				if (stack[index] != index) {
					end_of_unused_area = index;
					state = USEDSTACKCELL;
					updateBest(start_of_unused_area, end_of_unused_area);
				}
				break;
			}
			index++;
		}
		if (state == UNUSEDSTACKCELL) {
			updateBest(start_of_unused_area, end_of_unused_area);
		}
	}

	private void updateBest(int start_of_unused_area, int end_of_unused_area) {
		if (end_of_unused_area - start_of_unused_area > best_end_of_unused_area - best_start_of_unused_area) {
			best_end_of_unused_area = end_of_unused_area;
			best_start_of_unused_area = start_of_unused_area;
		}
	}
}
