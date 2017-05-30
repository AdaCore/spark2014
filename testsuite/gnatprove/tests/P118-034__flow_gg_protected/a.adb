package body A with Refined_State => (State_A => PO_A)
is

   Vol : Boolean with Volatile, Part_Of => PO_A;

   protected PO_A is
      procedure Read (X : out Boolean);
      procedure Write (X : Boolean);
   end PO_A;

   protected body PO_A is
      procedure Read (X : out Boolean)
      is
      begin
         X := Vol;
      end Read;

      procedure Write (X : Boolean)
      is
      begin
         Vol := X;
      end Write;
   end PO_A;

   procedure Access_A_In (X : out Boolean)
   is
   begin
      Po_A.Read (X);
   end Access_A_In;

   procedure Access_A_In_Out
   is
      Tmp : Boolean;
   begin
      Po_A.Read (Tmp);
      Tmp := not Tmp;
      Po_A.Write (Tmp);
   end Access_A_In_Out;

   procedure Access_A_Out
   is
   begin
      Po_A.Write (False);
   end Access_A_Out;

end A;
