package Invariants with SPARK_Mode is
   MMax : constant := 100;
   type My_Index is new Natural range 1 .. MMax;
   subtype My_Length is My_Index'Base range 0 .. MMax;
   type Element is new Natural;

   type Stack is private;

   function Max (S : Stack) return Element;

   function Size (S : Stack) return My_Length;

   procedure Push (S : in out Stack; E : Element) with
     Pre => Size (S) < My_Length'Last;

   procedure Push_Zero (S : in out Stack) with
     Pre => Size (S) < My_Length'Last;

   function Size return My_Length;

   procedure Push (E : Element) with
     Pre => Size < My_Length'Last;

   procedure Push_Zero with
     Pre => Size < My_Length'Last;

   type Stack_2 is private with Default_Initial_Condition => False;
private
   type Element_Array is array (My_Index) of Element;

   type Stack is record
      Content : Element_Array := (others => 0);
      Size    : My_Length := 0;
      Max     : Element := 0;
   end record with
     Type_Invariant => Is_Valid (Stack);

   function Is_Valid (S : Stack) return Boolean is
     ((for all I in 1 .. S.Size => S.Content (I) <= S.Max)
      and (if S.Max > 0 then
               (for some I in 1 .. S.Size => S.Content (I) = S.Max)));

   function Size (S : Stack) return My_Length is (S.Size);

   function Max (S : Stack) return Element is (S.Max);

   type Stack_2 is record
      Content : Element_Array;
      Size    : My_Length;
      Max     : Element;
   end record with
     Type_Invariant =>
       (for all I in 1 .. Stack_2.Size => Stack_2.Content (I) <= Stack_2.Max);
end Invariants;
