with Error;
use Error;

package Stacks is

   Empty_Stack_Str : constant String := "empty stack";

   type Element is new Integer;
   type Elements is array (Integer range <>) of Element;

   type Stack (Max : Positive) is tagged private;

   function Is_Empty (S : Stack) return Boolean;

   function Is_Full (S : Stack) return Boolean;

   function Size (S : Stack) return Natural;

   procedure Push (S : in out Stack; E : Element) with
     Pre'Class  => not S.Is_Full,
     Post'Class => S.Size = S.Size'Old + 1;

   procedure Pop (S : in out Stack);
   pragma Pre_Class (not S.Is_Empty);
   pragma Post_Class (S.Size = S.Size'Old - 1);

   function Peer (S : Stack) return Element with
     Pre'Class => not S.Is_Empty;

private

   type Stack (Max : Positive) is tagged record
      Top  : Natural := 0;
      Data : Elements (1 .. Max) := (others => 0);
   end record;

   function Size (S : Stack) return Natural is (S.Top);

   function Is_Empty (S : Stack) return Boolean is (S.Size = 0);

   function Is_Full (S : Stack) return Boolean is (S.Size = S.Max);

   function Peer (S : Stack) return Element is (S.Data (S.Top));

end Stacks;
