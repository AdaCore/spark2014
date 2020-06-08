package Nest_Return is
   --  Procedure which includes a simple return statement; this test is
   --  included to check the fix didn't break anything.
   procedure Nested_Proc (X : in Boolean; Y : out Boolean) with
      Post => Y = X;

      --  More complex version of Identity calling Nested_Proc and including a
      --  second simple return statement within a more deeply nested case.
   function Nesting_Func (X : Boolean) return Boolean with
      Post => Nesting_Func'Result = X;

      --  Function includes a procedure in a declare block, where that
      --  procedure has a simple return statement.
   function Declare_Block_Func (X : Boolean) return Boolean with
      Post => Declare_Block_Func'Result = X;

end Nest_Return;
