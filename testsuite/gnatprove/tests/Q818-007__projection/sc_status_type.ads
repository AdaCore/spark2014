package Sc_Status_Type is

   type Crash_Causing_Type is record
      X_1  : Boolean;
   end record;

   type Bit_Pattern_Type is record
      X_1  : Boolean;
      X_12 : Boolean;
   end record;

   type Duplicate_Status_Type is record
      Prime, Shadow : Bit_Pattern_Type;
   end record;

   type Object_Type is
      record
         Sc_State : Duplicate_Status_Type;
      end record;

   procedure Check (This : Object_Type);

end Sc_Status_Type;
