// Given a 2-dimensional array where the values along any row or any column
// is non-decreasing, and given a value "s" in the array, find an index
// "x,y" such that s==b[x,y].
// Note, due to a bug in the RiSE4fun version of Dafny, you cannot mention
// a 2-dimensional array element (like b[x,y]) in a loop guard or an if guard.
// Instead, first read such array elements into a local variable and then
// use the local variable in the while/if guards.

method Saddleback(b: array2<int>, value: int) returns (x: int, y: int)
  requires b != null;

  requires (forall i,j0,j1:int :: 0 <= i && i < b.Length0 && 
     0 <= j0 && j0 <= j1 && j1 < b.Length1 ==> b[i,j0] <= b[i,j1]);
 
  requires (forall i0, i1, j:int :: 0 <= i0 && i0 <= i1 && i1 < b.Length0 && 
     0 <= j && j < b.Length1 ==> b[i0,j] <= b[i1,j]);
   
  ensures x == -1 ==> 
     (forall i,j:int :: 0 <= i && i < b.Length0 &&
         0<=j && j < b.Length1 ==>
         b[i, j] != value);
      
  ensures x != -1 ==>
     0 <= x && x < b.Length0 && 0 <= y && y < b.Length1 && value == b[x,y];
{
  x := 0;
  y := b.Length1 - 1;

  while(x < b.Length0 && y >= 0)
    invariant 0 <= x && x <= b.Length0 &&
	-1 <= y && y < b.Length1 &&
	(forall i,j:int :: 0 <= i && i < b.Length0 &&
		0 <= j && j < b.Length1 ==>
			(i < x || j > y) ==> b[i, j] != value);

    decreases b.Length0 - x + y;
  {
    var k := b[x,y];

    if(k == value) {
	  return;
    }

    if(k < value) {
      x := x + 1;
    } else {
      y := y - 1;
    }

  }

  x := -1;
}
