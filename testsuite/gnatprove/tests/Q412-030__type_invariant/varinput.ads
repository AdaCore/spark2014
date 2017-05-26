package Varinput with
  SPARK_Mode
is
   type T1 is private;
   type T2 is private;

   G3 : Boolean := True;

   function F3 return Boolean is (G3);

   generic
      A : Boolean;
   function Func_Visible return Boolean;

   generic
      A : Boolean;
   package Pack_Visible is
   end;

private
   G : Boolean := True;
   G2 : Integer := 5;

   function F return Boolean is (G);
   function F2 return Integer is (G2);

   type T1 is new Integer with
     Type_Invariant => F;
   type T2 is new Integer with
     Predicate => F;
   type R (D : Boolean := F) is record
     A : Boolean := F;
     B : Integer;
   end record;

   type A is array (Integer range <>) of Integer;
   O : A (1 .. F2) := (others => 0);
   O2 : A renames O (F2 .. F2);
   O3 : Integer renames O (F2);

   generic
      A : Integer;
      B : Boolean;
   package P is
   end P;

   package Instance is new P (F2, True);

   generic
      O : Integer;
   function Func return Boolean;
end Varinput;
