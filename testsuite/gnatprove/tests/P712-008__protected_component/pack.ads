package Pack is

   type Rec is record
      X : Boolean := False;
   end record;

   type Arr is array (1 .. 10) of Boolean with Default_Component_Value => False;

   function Get (R : Rec) return Boolean is (R.X);
   procedure Set (R : out Rec);
   procedure Set (A : out Arr);

   protected type Prot is
      procedure P;
   private
      X : Rec;
      A : Arr;
   end Prot;

end Pack;
