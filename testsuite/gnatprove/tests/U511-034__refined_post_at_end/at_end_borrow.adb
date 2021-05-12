procedure At_End_Borrow with SPARK_Mode is
   type Rec is record
      I, J : aliased Integer;
   end record;

   function AE (X : access constant Rec) return access constant Rec is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function AE (X : access constant Integer) return access constant Integer is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   package Nested is
      function Get_I (X : not null access Rec) return not null access Integer with
        Post => X.I = Get_I'Result.all and AE (X).I = AE (Get_I'Result).all;
   end Nested;
   package body Nested is
      function Get_I (X : not null access Rec) return not null access Integer with
        Refined_Post => X.I = Get_I'Result.all and
        AE (X).all = (X.all with delta I => AE (Get_I'Result).all)
      is
      begin
         return X.I'Access;
      end Get_I;
      X : aliased Rec := (others => 1);
   begin
      declare
         Y : not null access Rec := X'Access;
         I : not null access Integer := Nested.Get_I (Y);
      begin
         I.all := 5;
      end;
      pragma Assert (X = (5, 1));
   end Nested;

   X : aliased Rec := (others => 1);
begin
   declare
      Y : not null access Rec := X'Access;
      I : not null access Integer := Nested.Get_I (Y);
   begin
      I.all := 5;
   end;
   pragma Assert (X.I = 5);
end At_End_Borrow;
