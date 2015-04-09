package Private_With_Attributes with SPARK_Mode is
   type Root is tagged record
      F : Natural;
   end record;
   type Child is new Root with private;

   type Root_Private_Tagged is tagged private with
     Default_Initial_Condition;
   type Child_Private_Tagged is new Root_Private_Tagged with private with
     Default_Initial_Condition;

   type Root_Discr (B : Boolean) is tagged private;

   type Private_Unconstrained (C : Natural := 0) is private with
     Default_Initial_Condition;
   subtype Private_Constrained is Private_Unconstrained (C => 0);

   C1 : constant Child;
   C2 : constant Child;
private
   pragma SPARK_Mode (Off);
   type Root_Private_Tagged is tagged record
      F : Natural := 0;
   end record;
   type Child_Private_Tagged is new Root_Private_Tagged with record
      F1 : Natural := 0;
   end record;

   type Root_Discr (B : Boolean) is tagged record
      case B is
         when True =>
            F : Natural := 0;
         when False =>
            null;
      end case;
   end record;

   type Private_Unconstrained (C : Natural := 0) is null record;
   type Child is new Root with record
      F1 : Natural := 0;
   end record;

   C1 : constant Child := (F => 1, F1 => 1);
   C2 : constant Child := (F => 1, F1 => 2);
end Private_With_Attributes;
