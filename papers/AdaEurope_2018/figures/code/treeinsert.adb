with Ada.Text_IO;
use Ada.Text_IO;



procedure treeinsert is

  type Rec;
  type Tree is access Rec;
  type Rec is record
	Data : Natural;
	Left, Right : Tree;
  end record;

  function buildLeaf (V : Natural) return Tree is
	T1 : Tree := new Rec;
	begin
	  T1.all.Data := V;
	  T1.all.Left := null;
	  T1.all.Right := null;
	return T1;
	end buildLeaf;

  procedure buildLeaf2 (T1 : in out Tree; V : Natural) is
	begin
	  T1.all.Data := V;
	  T1.all.Left := null;
	  T1.all.Right := null;
  end buildLeaf2;


procedure Insert (T : in Tree; V : Natural) is
  Walker : access Rec := T;
begin
  loop
	if V < Walker.Data then
	  if Walker.Left /= null then
		Walker := Walker.Left;
	  else
		Walker.Left := Build_Leaf(V);
		exit;
	  end if;
	elsif V > Walker.Data then
	  if Walker.Right /= null then
		Walker := Walker.Right;
	  else
		Walker.Right := Build_Leaf(V);
		exit;
	  end if;
	end if;
  end loop;
end Insert;

begin
  Put_Line("hi");
end treeinsert;


