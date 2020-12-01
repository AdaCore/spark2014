with Ada.Text_Io;
procedure Test_Fold with SPARK_Mode is
   type Pair is record
      Value  : Integer;
      Status : Boolean;
   end record;
   type Pair_Array is array (Positive range <>) of Pair;

   function P (X : Integer) return Boolean with Import;

   procedure Filter (A : in out Pair_Array) with
     Post => (for all I in A'Range => A (I).Value = A'Old (I).Value)
     and (for all I in A'Range =>
            A (I).Status = (A'Old (I).Status and P (A (I).Value)))
   is
   begin
      for K in A'Range when A (K).Status and then not P (A (K).Value) loop
         A (K).Status := False;
         pragma Loop_Invariant
           (for all I in A'First .. K =>
              A (I).Status = (A'Loop_Entry (I).Status and P (A (I).Value)));
      end loop;
   end Filter;

   procedure Filter_Rev (A : in out Pair_Array) with
     Post => (for all I in A'Range => A (I).Value = A'Old (I).Value)
     and (for all I in A'Range =>
            A (I).Status = (A'Old (I).Status and P (A (I).Value)))
   is
   begin
      for K in reverse A'Range when A (K).Status and then not P (A (K).Value) loop
         A (K).Status := False;
         pragma Loop_Invariant
           (for all I in K .. A'Last =>
              A (I).Status = (A'Loop_Entry (I).Status and P (A (I).Value)));
      end loop;
   end Filter_Rev;

   procedure Filter_Unroll (A : in out Pair_Array) with
     Pre  => A'First = 1 and A'Last = 5,
     Post => (for all I in A'Range => A (I).Value = A'Old (I).Value)
     and (for all I in A'Range =>
            A (I).Status = (A'Old (I).Status and P (A (I).Value)))
   is
   begin
      for K in 1 .. 5 when A (K).Status and then not P (A (K).Value) loop
         A (K).Status := False;
      end loop;
   end Filter_Unroll;

   procedure Bad with Pre => True is
   begin
      for I in 1 .. 30 when I / (I - 20) = 0 loop
         Ada.Text_IO.Put_Line (I'Image);
      end loop;
   end Bad;

   procedure OK with Pre => True is
   begin
      for I in 1 .. 30 when I /= 20 loop
         pragma Loop_Invariant (I / (I - 20) <= I);
         Ada.Text_IO.Put_Line (I'Image);
      end loop;
   end OK;

begin
   pragma Assert (for all I in 1 .. 20 when I mod 4 = 0 => I mod 2 = 0);
   pragma Assert (for some I in 1 .. 20 when I mod 3 = 0 => I mod 4 = 0);

   for I in 1 .. 30 when I mod 2 = 0 loop
      Ada.Text_IO.Put_Line (I'Image);
      pragma Assert (I mod 2 = 0);
   end loop;
end Test_Fold;
