with Error;
use Error;

package Stacks is
   pragma SPARK_Mode (Off);

   Empty_Stack_Str : constant String := "empty stack";

   type Element is new Integer;
   type Elements is array (Integer range <>) of Element;

   type Stack (Max : Positive) is tagged private;

   function Is_Empty (S : Stack) return Boolean;

   function Is_Full (S : Stack) return Boolean;

   function Size (S : Stack) return Natural;

   procedure Push (S : in out Stack; E : Element) with
     Pre  => not S.Is_Full,
     Post => S.Size = S.Size'Old + 1;

   procedure Pop (S : in out Stack);
   pragma Precondition (not S.Is_Empty);
   pragma Postcondition (S.Size = S.Size'Old - 1);

   function Peer (S : Stack) return Element with
     Pre => not S.Is_Empty;

private

   type Stack (Max : Positive) is tagged record
      Top  : Natural := 0;
      Data : Elements (1 .. Max);
   end record;

   function Size (S : Stack) return Natural is (S.Top);

   function Is_Empty (S : Stack) return Boolean is (S.Size = 0);

   function Is_Full (S : Stack) return Boolean is (S.Size = S.Max);

   function Peer (S : Stack) return Element is (S.Data (S.Top));

end Stacks;
