procedure Member with SPARK_Mode is
   subtype My_Count is Natural range 1 .. 5;

   type Nat_Array is array (Positive range <>) of  Natural;
   subtype Array_1_10 is Nat_Array (1 .. 10);

   function Init (C : My_Count) return Nat_Array is
     ((C .. C + 9 => 0));

   procedure Bad_1 is
      pragma Assert (Init (2) in Array_1_10); --@ASSERT:FAIL
   begin
      null;
   end Bad_1;

   procedure Bad_2 is
      A : Nat_Array := (1 .. 10 => 0);
   begin
      if A in Array_1_10 then
         pragma Assert (False); --@ASSERT:FAIL
      end if;
   end Bad_2;

   A : Nat_Array := (2 .. 11 => 0);

   pragma Assert (Init (1) in Array_1_10);
   pragma Assert (Init (1) in Init (2));
   pragma Assert (Init (1) in Init (2) | Init (3));
   pragma Assert (Init (1) in Array_1_10 | (1 .. 10 => 1));
begin
   if A in Array_1_10 then
      pragma Assert (False);
   end if;
end Member;
