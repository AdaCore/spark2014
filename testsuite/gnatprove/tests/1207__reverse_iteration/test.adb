procedure Test with SPARK_Mode is

   type Int_Array is array (Positive range 1 .. 100) of Integer;

   type Container is record
      Content : Int_Array;
      Top : Natural;
   end record with Predicate => Top in 0 .. 100,
     Iterable =>
       (Has_Element => Has_Element,
        First => First,
        Next => Next,
        Last => Last,
        Previous => Previous);

   type Cursor is record
      Position : Natural;
   end record;

   function Has_Element (C : Container; P : Cursor) return Boolean is
      (P.Position in 1 .. C.Top);

   function First (C : Container) return Cursor is (Position => 1);
   function Next (C : Container; P : Cursor) return Cursor is
     (Position => P.Position + 1)
   with Pre => Has_Element (C, P);

   function Last (C : Container) return Cursor is (Position => C.Top);
   function Previous (C : Container; P : Cursor) return Cursor is
     (Position => P.Position - 1)
     with Pre => Has_Element (C, P);

   procedure Test_OK (C : in out Container) is
   begin
      for P in reverse C loop
         C.Content (P.Position) := 0;
         pragma Loop_Invariant
           (for all P2 in C =>
              (if P2.Position >= P.Position then C.Content (P2.Position) = 0));
      end loop;
      pragma Assert (for all P2 in C => C.Content (P2.Position) = 0);
   end Test_OK;

   procedure Test_Bad (C : in out Container) is
   begin
      for P in reverse C loop
         C.Content (P.Position) := 0;
         pragma Loop_Invariant
           (for all P2 in C =>
              (if P2.Position <= P.Position then C.Content (P2.Position) = 0));
      end loop;
      pragma Assert (for all P2 in C => C.Content (P2.Position) = 0);
   end Test_Bad;

begin
   null;
end;
