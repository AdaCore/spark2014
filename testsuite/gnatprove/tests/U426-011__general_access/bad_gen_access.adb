with Unchecked_Deallocation;

procedure Bad_Gen_Access with SPARK_Mode is
   type Gen_Int is access all Integer;
   type Cst_Int is access constant Integer;

   function F (X : Cst_Int) return Boolean with Import;

   procedure Bad is new Unchecked_Deallocation (Integer, Gen_Int); --  Bad, general access types cannot be deallocated

   X : Gen_Int := new Integer'(12); --  Bad allocators on general access types can only occur at library level
   I : aliased Integer := 12;
   function F return Gen_Int with Import;
   Y : Gen_Int := F;
   Z : Cst_Int := Cst_Int (Y); --  Move as part of conversion to access-to-constant type not yet supported
   pragma Assert (F (Cst_Int (Y))); --  Bad conversions to access-to-constant types can only occur at library level
begin
   declare
      type Loc_Int is access all Integer;
      I : aliased Integer := 12;
      B : access Integer := I'Access;
      W : Loc_Int;
   begin
      W := Loc_Int (B); --  Bad conversion from an anonymous access type to a named access type
   end;
end Bad_Gen_Access;
