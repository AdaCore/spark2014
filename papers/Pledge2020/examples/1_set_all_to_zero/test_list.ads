package Test_List with SPARK_Mode is
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Data : Integer;
      Next : List;
   end record;

   type My_Nat is new Natural;
   subtype My_Pos is My_Nat range 1 .. My_Nat'Last;

   function "+" (X, Y : My_Nat) return My_Nat is
     (if My_Nat'Last - X < Y then My_Nat'Last
      else My_Nat (Integer (X) + Integer (Y)));
   --  Saturating addition to simplify contracts

   function Length (L : access constant List_Cell) return My_Nat is
     (if L = null then 0 else Length (L.Next) + 1)
   with Ghost,
        Annotate => (GNATprove, Terminating);
   --  Number of elements in the list. Returns My_Nat'Last if there is more
   --  than My_Nat'Last elements in the list.

   pragma Annotate
     (GNATprove, False_Positive, """Length"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   function Nth (L : access constant List_Cell; N : My_Pos) return Integer is
     (if N = 1 then L.Data else Nth (L.Next, N - 1))
   with Ghost,
        Annotate => (GNATprove, Terminating),
        Pre => N <= Length (L);
   --  Element at position N in the list

   pragma Annotate
     (GNATprove, False_Positive, """Nth"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   function Pledge
     (Dummy    : access constant List_Cell;
      Property : Boolean) return Boolean
   is
     (Property)
   with Ghost,
     Annotate => (GNATprove, Pledge);
   --  Pledge function, used to mark assertions as pledges for the analysis tool

   procedure Set_All_To_Zero (X : List) with
     Pre  => Length (X) < My_Nat'Last,
     Post => Length (X) = Length (X)'Old
     and (for all I in 1 .. Length (X) => Nth (X, I) = 0);
   --  Set all elements of a list to 0

end Test_List;
