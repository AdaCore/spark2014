procedure Main with SPARK_Mode is

   --  An discriminated record type and a derived Unchecked_Union type

   type Rec_Typ (I : Integer := 0) is record
      Comp_0 : Integer := 0;
      Comp_1 : Integer := 1;
      case I is
         when 0 =>
            Comp_2 : Integer := 2;
         when 1 =>
            Comp_3 : Integer;
         when 2 =>
            Comp_4 : Integer := 4;
         when 3 =>
            Comp_5 : Integer;
         when others =>
            Comp_Other : Integer;
      end case;
   end record;

   type Derived_U_U is new Rec_Typ with Unchecked_Union;

   X : Derived_U_U := (I => 0, others => 0);
   Y : Rec_Typ := Rec_Typ (X);--@UU_RESTRICTION:FAIL
begin
   null;
end Main;
