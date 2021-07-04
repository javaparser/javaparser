// This is Challenge 2A from VerifyThis 2019

public class Challenge2A {

    //@ public normal_behavior
    //@ assigns \nothing;
    //@ ensures \result.length == input.length;
    //@ ensures \forall int i; 0 <= i < \result.length; \result[i] < i; // left-neighbor is to the left
    //@ ensures \forall int i; 0 <= i < \result.length; \result[i] != -1 ==> input[\result[i]] < input[i]; // LN has smaller value
    //@ ensures \forall int i; 0 <= i < \result.length; \forall int j; \result[i] < j < i; input[j] >= input[i]; // LN is closest smaller value
    public int[] leftNeighbors(int[] input) {

        int[] left = new int[input.length];
        int[] stack = new int[input.length];
        int height = 0;

        //@ loop_invariant 0 <= x <= input.length;
        //@ loop_invariant 0 <= height <= x;
        //@ loop_invariant \forall int i; 0 <= i < x; left[i] < i;  // so far, all left-neighbors are to the left
        //@ loop_invariant \forall int i; 0 <= i < x; left[i] != -1 ==> input[left[i]] < input[i]; // so far, all LNs have smaller values
        //@ loop_invariant \forall int i; 0 <= i < x; \forall int j; left[i] < j < i; input[j] >= input[i]; // so far, all LNs are closest smaller values
        //@ loop_invariant \forall int i; 0 <= i < height; 0 <= stack[i] < x; // all stack values are legitimate positions
        //@ loop_invariant x > 0 ==> height > 0;
        //@ loop_invariant height > 0 ==> stack[height-1] == x-1; // x is always one more than top of stack (after the first iteration)
        //@ loop_invariant \forall int i; 1 <= i < height; \forall int j; stack[i-1] < j < stack[i]; input[j] >= input[stack[i]]; // items missing from stack are larger than something to their right
        //@ loop_invariant height > 0 ==> \forall int j; 0 <= j < stack[0]; input[j] >= input[stack[0]]; // items missing from the stack in the first segment are larger than stack[0]
        //@ loop_decreases input.length - x;
        for (int x=0; x<input.length; x++) {
            //@ loop_invariant 0 <= height <= x;
            //@ loop_invariant \forall int i; 0 <= i < x; left[i] < i;   // so far, all left-neighbors are to the left
            //@ loop_invariant \forall int i; 0 <= i < height; 0 <= stack[i] < x;  // so far, all LNs have smaller values
            //@ loop_invariant \forall int i; 1 <= i < height; \forall int j; stack[i-1] < j < stack[i]; input[j] >= input[stack[i]];  // so far, all LNs are closest smaller values
            //@ loop_invariant height > 0 ==> \forall int j; stack[height-1] < j < x; input[j] >= input[x]; // Everything between top of stack and x is larger than va
            //@ loop_invariant height == 0 ==> \forall int j; 0 <= j < x; input[j] >= input[x]; // If height is 0, everything to the left is smaller than value at current position
            //@ loop_decreases height;
            while (height > 0 && input[stack[height-1]] >= input[x]) {
                height--;
            }

            if (height == 0) {
                left[x] = -1;
            } else {
                left[x] = stack[height-1];
            }
            stack[height++] = x;
        }
        return left;
    }
}
