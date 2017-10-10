package body Foo with Refined_State => (S => PO)
is

   protected PO is
      procedure Set (X : Boolean);
      function Get return Boolean;
   private
      Data : Boolean := False;
   end PO;

   protected body PO with SPARK_Mode => Off is
      procedure Set (X : Boolean)
      is
      begin
         Data := X;
      end Set;

      function Get return Boolean is (Data);
   end PO;

   procedure Set (X : Boolean)
   with Refined_Global => (Output => PO)
   is
   begin
      PO.Set (X);
   end Set;

   procedure Get (X : out Boolean)
   with Refined_Global => PO
   is
   begin
      X := PO.Get;
   end Get;

end Foo;
