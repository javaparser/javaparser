class Queens {   

    /*@ private normal_behaviour
      @   //pos is within bounds
      @   requires 0 <= pos && pos < board.length;
      @
      @   //the return value indicates whether the queen in column pos 
      @   //conflicts with a queen in a column to the left of pos
      @   ensures \result == (\forall int x; 0 <= x && x < pos; 
      @                                      board[x] != board[pos] 
      @                                      && board[x] - board[pos] != pos - x 
      @                                      && board[pos] - board[x] != pos - x);
      @*/
    private static /*@pure@*/ boolean isConsistent(int[] board, int pos) {
	/*@ loop_invariant
	  @   //q is a column to the left of pos 
	  @   0 <= q && q <= pos 
	  @
	  @   //for all columns up to q, there is no conflict with the queen in 
	  @   //column pos
	  @   && (\forall int x; 0 <= x && x < q; 
	  @                      board[x] != board[pos] 
          @                      && board[x] - board[pos] != pos - x 
          @                      && board[pos] - board[x] != pos - x);
          @
	  @ assignable \nothing;
	  @ decreases pos - q;
	  @*/
	for(int q = 0; q < pos; q++) {
	    if (!((board[q] != board[pos])
	           && (board[q] - board[pos] != pos - q)
		   && (board[pos] - board[q] != pos - q))) {
		return false;
	    }
	}
	return true;
    }
    
    
    /*@ private normal_behaviour
      @   //pos is within bounds
      @   requires 0 <= pos && pos < board.length;
      @  
      @   //the row numbers in the board are valid 
      @   requires (\forall int x; 0 <= x && x < board.length; 
      @                            0 <= board[x] && board[x] < board.length);
      @
      @   //there is no conflict in the columns to the left of pos 
      @   requires (\forall int p, x; 0 <= x && x < p && p < pos;
      @                               board[x] != board[p] 
      @                               && board[x] - board[p] != p - x 
      @                               && board[p] - board[x] != p - x);
      @
      @   //the row numbers in the board are still valid
      @   ensures (\forall int x; 0 <= x && x < board.length; 
      @                           0 <= board[x] && board[x] < board.length);
      @
      @   //if the return value is true, then there are no conflicts on the board
      @   ensures \result ==> (\forall int p, x; 0 <= x && x < p && p < board.length;  
      @                                          board[x] != board[p] 
      @                                          && board[x] - board[p] != p - x 
      @                                          && board[p] - board[x] != p - x);
      @
      @   //if the return value is false, then there is no solution that starts 
      @   //with the queens in the columns to the left of pos
      @   ensures !\result ==> !(\exists \seq s; s.length == board.length;
      @                                          (\forall int x; 0 <= x && x < s.length; 
      @                                                          0 <= (int)s[x] && (int)s[x] < s.length)
      @                                          && (\forall int p, x; 0 <= x && x < p && p < s.length;  
      @                                                                (int)s[x] != (int)s[p] 
      @                                                                && (int)s[x] - (int)s[p] != p - x 
      @                                                                && (int)s[p] - (int)s[x] != p - x)
      @                                          && (\forall int x; 0 <= x && x < pos; (int)s[x] == \old(board[x])));
      @
      @   assignable board[pos..board.length-1];
      @   measured_by board.length - pos;
      @*/    
    private static /*@nullable@*/ boolean search(int pos, int[] board) {
	/*@ loop_invariant
	  @   //i is within bounds 
	  @   0 <= i && i <= board.length
	  @
	  @   //the row numbers in the board are still valid
	  @   && (\forall int x; 0 <= x && x < board.length; 0 <= board[x] && board[x] < board.length)
	  @
	  @   //for all row numbers j between 0 and i: there is no solution that
	  @   //starts with the queens in the columns to the left of pos and 
	  @   //uses j at column pos
	  @   && (\forall int j; 0 <= j && j < i;
	  @                      !(\exists \seq s; s.length == board.length;
          @                                        (\forall int x; 0 <= x && x < s.length; 
          @                                                        0 <= (int)s[x] && (int)s[x] < s.length)  
          @                                        && (\forall int p, x; 0 <= x && x < p && p < s.length;  
          @                                                              (int)s[x] != (int)s[p] 
          @                                                               && (int)s[x] - (int)s[p] != p - x 
          @                                                               && (int)s[p] - (int)s[x] != p - x)
          @                                        && (\forall int x; 0 <= x && x < pos; (int)s[x] == \old(board[x]))
          @                                        && (int)s[pos] == j));
          @
	  @ assignable board[pos..board.length-1];
	  @ decreases board.length - i;
	  @*/
	for(int i = 0; i < board.length; i++) {
	    board[pos] = i;
	    if(isConsistent(board, pos)) {
		if(pos == board.length - 1) {
		    return true;
		} else {
		    boolean complete = search(pos + 1, board);
		    if(complete) {
			return true;
		    }
		}
	    }
	}
	return false;
    }
    
    
    /*@ public normal_behaviour
      @   //n must be positive
      @   requires 0 < n;
      @
      @   //if the return value is not null, then it is a solution
      @   ensures \result != null ==> \result.length == n
      @                               && (\forall int x; 0 <= x && x < n; 
      @                                                  0 <= \result[x] && \result[x] < n)
      @                               && (\forall int p, x; 0 <= x && x < p && p < n;  
      @                                                     \result[x] != \result[p] 
      @                                                     && \result[x] - \result[p] != p - x 
      @                                                     && \result[p] - \result[x] != p - x);
      @
      @   //if the return value is null, then there is no solution
      @   ensures \result == null ==> !(\exists \seq s; s.length == n 
      @                                                 && (\forall int x; 0 <= x && x < n; 
      @                                                                    0 <= (int)s[x] && (int)s[x] < n)
      @                                                 && (\forall int p, x; 0 <= x && x < p && p < n;  
      @                                                                       (int)s[x] != (int)s[p] 
      @                                                                       && (int)s[x] - (int)s[p] != p - x 
      @                                                                       && (int)s[p] - (int)s[x] != p - x));
      @*/        
    public static /*@pure nullable@*/ int[] nQueens(int n) {
	int[] board = new int[n];
	// FIXME the development of model methods implmentation revealed
	// that this problem is very sensitive to quantifier instantiation
	// mischaps, see bug #1370. Changing the if statement into ? : seems
	// to solve the problem. 
	/*
	if(search(0, board)) {
	    return board;
	}else{
	    return null;
	}
	*/
	return search(0, board) ? board : null;
    }
    
    
        
    /*public static void main(String[] args) {
	int[] board = nQueens(8);
	if(board != null) {
    	    for(int i = 0; i < board.length; i++) {
    		for(int j = 0; j < board.length; j++) {
    		    System.out.print(j == board[i] ? "X" : "O");
    		}
    		System.out.print("\n");
    	    }
	} else {
	    System.out.println("no solution found");
	}
    }*/
}
