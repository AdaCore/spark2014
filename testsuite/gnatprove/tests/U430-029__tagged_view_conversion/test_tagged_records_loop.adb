procedure Test_Tagged_Records_Loop with SPARK_Mode is
   type Root is tagged record
      F : Integer;
      I : Integer;
   end record;
   type Child is new Root with record
      G : Integer;
      J : Integer;
   end record;
   type Root_Acc is access Root'Class;
   type Root_Array is array (1 .. 100) of not null Root_Acc;

   procedure Init_2 (A : in out Root_Array) with
     Pre =>  (for all K in A'Range => A (K).I = 1 and
               (if A (K).all in Child'Class then Child'Class (A (K).all).J = 2))
   is
   begin
      for I in A'Range loop
         A (I).F := 0;
         if A (I).all in Child'Class then
            Child'Class (A (I).all).G := 0;
         end if;
      end loop;
      pragma Assert
        (for all K in A'Range => A (K).I = 1);
         --  Frame condition is generated, I is visible in Root
      pragma Assert
        (for all K in A'Range =>
           (if A (K).all in Child'Class then Child'Class (A (K).all).J = 2));
         --  Frame condition is not generated as J is not visible in Root
   end Init_2;

   procedure Init (A : in out Root_Array) with
     Pre => (for all K in A'Range => A (K).I = 1 and
               (if A (K).all in Child'Class then Child'Class (A (K).all).J = 2)),
     Post =>
       (for all K in A'Range =>
          (if A (K).all in Child'Class then Child (A (K).all) = (0, 1, 0, 2)
           else Root (A (K).all) = (0, 1)))
   is
   begin
      for I in A'Range loop
         A (I).F := 0;
         if A (I).all in Child'Class then
            Child'Class (A (I).all).G := 0;
         end if;
         pragma Loop_Invariant
           (for all K in A'First .. I => A (K).F = 0);
         pragma Loop_Invariant
           (for all K in A'First .. I =>
              (if A (K).all in Child'Class then Child'Class (A (K).all).G = 0));
         pragma Loop_Invariant
           (for all K in A'Range =>
              (if A (K).all in Child'Class then Child'Class (A (K).all).J = 2));
      end loop;
   end Init;
begin
   null;
end Test_Tagged_Records_Loop;
