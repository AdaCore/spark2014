procedure Main is 
   type Rec is record
      Comp : Natural := 1234;
   end record;

   subtype Index is Integer range 1 .. 10;
   type Arr is array (Index) of Rec;

   Cheat : Boolean := True;

   function Get_Rec return Rec with 
     Post => Get_Rec'Result = Rec'(Comp => 5678);
   
   function Get_Arr return Arr with
     Post => Get_Arr'Result = Arr'(others => Rec'(Comp => 9012));
     
   function Get_Index return Index with
     Post => (if Cheat then Get_Index'Result = 3 else Get_Index'Result = 5);

   function Get_Rec return Rec is
      Result : constant Rec := Rec'(Comp => 5678);
   begin
      return Result;
   end Get_Rec;

   function Get_Arr return Arr is
      Result : constant Arr := (others => Rec'(Comp => 9012));
   begin
      return Result;
   end Get_Arr;

   function Get_Index return Index is
   begin
      if Cheat then
         return 3;
      end if;

      return 5;
   end Get_Index;

   Arr_Obj : Arr := Get_Arr;
   Rec_Obj : Rec := Get_Rec;

   Obj_1 : Rec     renames Arr_Obj (1);
   Obj_2 : Rec     renames Arr_Obj (Get_Index);
   Obj_3 : Rec     renames Get_Arr (Get_Index);
   Obj_4 : Natural renames Rec_Obj.Comp;
   Obj_5 : Natural renames Get_Rec.Comp;
   Obj_6 : Natural renames Get_Arr (Get_Index).Comp;
       
   procedure Set_Obj_1 is
   begin
      Obj_1 := (Comp => 0);
   end Set_Obj_1;
   
   procedure Set_Obj_2 is
   begin
      Obj_2.Comp := Obj_2.Comp + 1;
   end Set_Obj_2;
   
   procedure Set_Obj_4 is
   begin
      Obj_4 := 0;
   end Set_Obj_4;
   
begin
   Cheat := False;
   
   pragma Assert (Obj_1.Comp = 9012);
   pragma Assert (Obj_2.Comp = 9012);
   pragma Assert (Obj_3.Comp = 9012);
   pragma Assert (Obj_4 = 5678);
   pragma Assert (Obj_5 = 5678);
   pragma Assert (Obj_6 = 9012);
   
   Set_Obj_1;
   Set_Obj_2;
   Set_Obj_4;
   
   --  It should not be possible to prove the assertions below, after the
   --  calls to Set_Obj_?
   
   pragma Assert (Obj_1.Comp = 9012);
   pragma Assert (Obj_2.Comp = 9012);
   pragma Assert (Obj_4 = 5678);

end Main;
