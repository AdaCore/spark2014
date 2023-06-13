procedure Main with SPARK_Mode is
   type Int_Acc is access Integer;
   type Int_Arr is array (Positive range <>) of Integer;
   type Arr_Acc is access Int_Arr;

   procedure Set (X : in out Integer) with Import;

   --  Qualified expressions give a constant view of their prefix. Updates
   --  to paths going through a qualified expression are disallowed.

   procedure Set (X : not null Int_Acc) is
   begin
      --  Direct assignment

      Int_Acc'(X).all := 24;

      --  Parameter passing

      Set (Int_Acc'(X).all);

      --  Borrows

      declare
         Y : access Integer := Int_Acc'(X).all'Access;
      begin
         Y.all := 24;
      end;
   end Set;

   --  Test that we reject the same in for of loops

   procedure Set (X : not null Arr_Acc) is
   begin
      for E of Arr_Acc'(X).all loop
         E := 12;
         Set (E);
      end loop;
   end Set;
begin
   null;
end Main;
