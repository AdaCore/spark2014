package Stacks is

   Max : constant Positive := 10;

   subtype IntMax is Integer range 0 .. Max;
   type Elements is array (IntMax) of Integer;

   function Size (Top : IntMax; Data : Elements) return Natural is (Top);

   function Is_Empty (Top : IntMax; Data : Elements) return Boolean is (Size (Top, Data) = 0);

   function Is_Full (Top : IntMax; Data : Elements) return Boolean is (Size (Top, Data) = Max);

   function Peer (Top : IntMax; Data : Elements) return Integer is (Data (Top));

   procedure Push (Top : in out IntMax; Data : in out Elements; E : Integer) with
     Pre  => not Is_Full (Top, Data),
     Post => Size (Top, Data) = Size (Top'Old, Data'Old) + 1;

   procedure Pop (Top : in out IntMax; Data : in out Elements);
   pragma Precondition (not Is_Empty (Top, Data));
   pragma Postcondition (Size (Top, Data) = Size (Top'Old, Data'Old) - 1);

end Stacks;
