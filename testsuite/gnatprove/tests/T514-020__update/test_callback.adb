procedure Test_Callback with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;

   procedure Update_All
     (A          : in out Nat_Array;
      Update_One : not null access procedure (X : in out Natural))
   is
   begin
      for E of A loop
         Update_One (E);
      end loop;
   end Update_All;

   function In_Range (X : Natural) return Boolean with Import;

   function Relation (X, Y : Natural) return Boolean with Import;

   procedure Update_One_1 (X : in out Natural) with Import,
     Post => Relation (X'Old, X);

   procedure Test_1 (A : in out Nat_Array) with Pre => True is
   begin
      Update_All (A, Update_One_1'Access);
   end Test_1;

   procedure Update_One_2 (X : in out Natural) with Import,
     Pre  => In_Range (X),
     Post => Relation (X'Old, X);

   procedure Test_2 (A : in out Nat_Array) with Pre => True is
   begin
      Update_All (A, Update_One_2'Access);
   end Test_2;

   type Update_Proc is not null access procedure (X : in out Natural) with
     Pre  => In_Range (X),
     Post => Relation (X'Old, X);

   procedure Update_All_2
     (A          : in out Nat_Array;
      Update_One : Update_Proc)
   with Pre  => (for all E of A => In_Range (E)),
        Post => (for all I in A'Range => Relation (A'Old (I), A (I)))
   is
   begin
      for K in A'Range loop
         Update_One (A (K));
         pragma Loop_Invariant
           (for all I in A'First .. K => Relation (A'Loop_Entry (I), A (I)));
      end loop;
   end Update_All_2;

   procedure Test_3 (A : in out Nat_Array) with Pre => (for all E of A => In_Range (E)) is
   begin
      Update_All_2 (A, Update_One_2'Access);
   end Test_3;

   procedure Update_One_3 (X : in out Natural) with Import,
     Pre  => In_Range (X);

   procedure Test_4 (A : in out Nat_Array) with Pre => (for all E of A => In_Range (E)) is
   begin
      Update_All_2 (A, Update_One_3'Access);
   end Test_4;
begin
   null;
end Test_Callback;
