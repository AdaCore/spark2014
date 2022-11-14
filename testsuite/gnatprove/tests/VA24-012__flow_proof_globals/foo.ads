package Foo
with
   Abstract_State    => State,
   Initializes       => State,
   Initial_Condition => Is_Valid
is
   function Is_Valid return Boolean;
   function Get_Index return Integer;

private
   Index : Integer := 0 with Part_Of => State;

   function Get_Index return Integer is (Index);

   function Check (Idx : Integer) return Boolean is (Idx = Get_Index);
end Foo;
