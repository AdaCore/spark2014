with Ada.Text_IO;
use Ada.Text_IO;



procedure maxtree with SPARK_Mode is

  type Rec;
  type Tree is access Rec;
  type Rec is record
	Data : Natural;
	Left, Right : Tree;
  end record;

function Max (T : in Tree) return Integer is 
  Walker : access constant Rec := T; -- Walker observes T
  Value  : Natural := 0;
begin     
  while Walker /= null loop
	if Walker.Data > Max then
	  Max := Walker.Data;
	end if;
	Walker := Walker.Right; -- assignment to Walker 
  end loop;
end Max;

  Tree_var : Owning_Tree_Ptr := Build_Tree(...);
  Y : Natural;

begin
  Y := Max (Tree_var);
  (...)
end maxtree;


