with Ada.Text_IO;

procedure Main with SPARK_Mode is
   type Int_Ptr is access Integer;

   procedure Zero_First_Arg(X : access Integer; Y : access Integer)
     with Pre => (X /= null and Y /= null),
          Post => (Y.all = Y.all'Old and X.all = 0) is
   begin
      X.all := 0;
      -- silence spurious warning about Zero_First_Arg having no effect
      Ada.Text_IO.New_Line;
   end Zero_First_Arg;

   X : Int_Ptr := new Integer'(1);
begin
   Zero_First_Arg(X,X);
   pragma Assert (X.all /= 0);
   if (X.all = 0) then
      Ada.Text_IO.Put_Line("It's 0!");
   end if;

end Main;
