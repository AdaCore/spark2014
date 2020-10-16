with Ada.Text_IO; use Ada.Text_IO;

procedure Global_Access_In with SPARK_Mode is
   type Int_Ptr is access Integer;
   My_Int_Ptr : Int_Ptr;

   I : Integer := 1;
   My_Global : constant Int_Ptr := new Integer'(I);

   C : constant Integer := 2;
   Const_Global : constant Int_Ptr := new Integer'(C);

--   type Acc_Const is access constant Integer;
--   My_Const : aliased constant Integer := 3;
--   Point_To_Const : Acc_Const := Acc_Const'(My_Const);
   -- illegal in SPARK

   procedure Zero_Global_Ptr_Contents
     with Global => (In_Out => My_Global)
   is
   begin
      My_Global.all := 0;
   end Zero_Global_Ptr_Contents;

   procedure Copy_Global_Ptr_Contents
     with Global => (Input => Const_Global,
                     In_Out => My_Global)
   is
   begin
      My_Global.all := Const_Global.all;
   end Copy_Global_Ptr_Contents;

   procedure Copy_Ptr_To_Global (X : access constant Integer)
     with Pre    => X /= null,
          Global => (In_Out => My_Global) is
   begin
      My_Global.all := X.all;
   end Copy_Ptr_To_Global;

   procedure Copy_To_Const_Global (N : Integer)
     with Global => (In_Out => Const_Global) is
   begin
      Const_Global.all := N;  --  should be illegal
   end Copy_To_Const_Global;

begin
   --  Evidence that the contents of a 'constant pointer'
   --  can be written to.
   Zero_Global_Ptr_Contents;
   if My_Global.all = 0 then
      Put_Line("My Global is 0!");
   end if;

   --  Showing access constant
   Put_Line("Const_Global was" & Const_Global.all'Img);
   Copy_To_Const_Global (I);
   Put_Line("Const_Global is now" & Const_Global.all'Img);
   Copy_To_Const_Global (C);
   Put_Line("Const_Global is now" & Const_Global.all'Img);

   Put_Line("My_Global was" & My_Global.all'Img);
   Copy_Global_Ptr_Contents;
   Put_Line("Copied Const_Global into My_Global which is now"
                        & My_Global.all'Img);

   My_Int_Ptr := new Integer'(I);
   --  Legal use of an access contant type (as a formal parameter)
   --  showing the copy routine works
   Copy_Ptr_To_Global (X => My_Int_Ptr);
   Put_Line("My_Global is " & My_Global.all'Img);

   --  This is an alias; ticket T527-057 to deal with faulty alias
   --  detection in this case
   Copy_Ptr_To_Global (X => My_Global);  --  @ALIASING:CHECK
   Put_Line("Due to aliasing My_Global is " & My_Global.all'Img);
end;
