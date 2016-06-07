with Declare_Iterable; use Declare_Iterable;

procedure For_Loop_Iterable with SPARK_Mode is

   type Container_Holder is record
      Content : Container;
   end record;

   A : Nat_Array := (others => 0);
   G : Container := From_Nat_Array (A);
   H : Container_Holder := (Content => G);
begin
   for E of From_Nat_Array (A) loop
      A (2) := 1;
      pragma Assert (E = 0);-- OK
   end loop;
   for E of Nat_Array'(others => A (1)) loop
      A (1) := 1;
      pragma Assert (E = 0);-- OK
   end loop;
   for E of G loop
      Set (G, 2, 1);
      pragma Assert (E = 0);--@ASSERT:FAIL
   end loop;
   for E of H.Content loop
      Set (H.Content, 2, 1);
      pragma Assert (E = 0);--@ASSERT:FAIL
   end loop;
end For_Loop_Iterable;
