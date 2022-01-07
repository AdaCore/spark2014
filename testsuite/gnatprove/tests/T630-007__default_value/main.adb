procedure Main with SPARK_Mode is
   function Id (X : Positive) return Positive is (X);

   type My_Int is new Integer with Default_Value => 0;
   type Arr_1 is array (Positive range <>) of My_Int;
   type Arr_2 is array (Positive range <>) of Integer with
     Default_Component_Value => 0;

   type Holder1 is record
      V : Arr_1 (1 .. Id (5));
   end record;
   type Holder2 is record
      V : Arr_2 (1 .. Id (5));
   end record;

   type Int_Acc is access Integer;
   type H is record
      A : Int_Acc;
   end record;
   type H_Acc is access H;

begin
   pragma Assert (new H /= null);
   pragma Assert
     (for all I in 1 .. 5 =>
        Integer (Holder1'(others => <>).V (I)) = Holder2'(V => <>).V (I));
end;
