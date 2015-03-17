procedure Dynamic_Array (C : Natural) with SPARK_Mode is
   subtype My_Nat  is Natural range 0 .. C;
   type Rec (B : Boolean := True) is record
      case B is
         when True =>
            F1 : My_Nat;
         when False =>
            F2 : My_Nat;
      end case;
   end record;

   type Rec_Array is array (Positive range <>) of Rec;

   type Holder (D : Natural) is record
      Content : Rec_Array (1 .. D);
   end record;

   function New_Holder (D : Natural) return Holder with
     Post => (if C = 0 then New_Holder'Result.D = 0
                else New_Holder'Result.D = D);

   function New_Holder (D : Natural) return Holder is
   begin
      if C = 0 then
         return (D => 0, Content => (1 .. 0 => (B => True, F1 => C)));
      else
         return (D => D, Content => (1 .. D => (B => True, F1 => C)));
      end if;
   end New_Holder;

   function Increment (R : Rec) return Natural is
     (if R.B then (if R.F1 < C then R.F1 + 1 else R.F1)
      else (if R.F2 < C then R.F2 + 1 else R.F2));

   H : Holder (C) := (D => C, Content => (1 .. C => (B => False, F2 => C)));
begin
   pragma Assert (H.D = New_Holder (C).D);
   for I in 1 .. C loop
      pragma Loop_Invariant
        (for all J in 1 .. I - 1 => H.Content (J).B and then
         H.Content (J).F1 = Increment (New_Holder (C).Content (J)));
      pragma Loop_Invariant
        (for all J in I .. C => not H.Content (J).B);
      declare
         HH : constant Holder := New_Holder (C);
         R  : constant Rec := HH.Content (I);
         F  : Natural;
      begin
         if R.B then
            F := R.F1;
         else
            F := R.F2;
         end if;

         if F < C then
            F := F + 1;
         end if;

         H.Content (I) := (B => True, F1 => F);
      end;
   end loop;
end Dynamic_Array;
