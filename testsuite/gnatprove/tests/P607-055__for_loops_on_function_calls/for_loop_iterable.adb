with Declare_Iterable; use Declare_Iterable;

procedure For_Loop_Iterable with SPARK_Mode is

   type Container_Holder is record
      Content : Container;
   end record;

   procedure P1 with Pre => True is
      A : Nat_Array := (others => 0);
   begin
      for E of From_Nat_Array (A) loop
         A (2) := 1;
         pragma Assert (E = 0);-- OK
      end loop;
   end P1;

   procedure P2 with Pre => True is
      A : Nat_Array := (others => 0);
   begin
      for E of A loop
         A (2) := 1;
         pragma Assert (E = 0);--@ASSERT:FAIL
      end loop;
   end P2;

   procedure P3 with Pre => True is
      A : Nat_Array := (others => 0);
      G : Container := From_Nat_Array (A);
   begin
      for E of G loop
         Set (G, 2, 1);
         pragma Assert (E = 0);--@ASSERT:FAIL
      end loop;
   end P3;

   procedure P4 with Pre => True is
      A : Nat_Array := (others => 0);
      G : Container := From_Nat_Array (A);
      H : Container_Holder := (Content => G);
   begin
      for E of H.Content loop
         Set (H.Content, 2, 1);
         pragma Assert (E = 0);--@ASSERT:FAIL
      end loop;
   end P4;

   procedure P5 with Pre => True is
      A : Nat_Array := (others => 0);
   begin
      for E of Nat_Array'(others => A (1)) loop
         A (1) := 1;
         pragma Assert (E = 1);--@ASSERT:FAIL
      end loop;
   end P5;

begin
   P1;
   P2;
   P3;
   P4;
   P5;
end For_Loop_Iterable;
