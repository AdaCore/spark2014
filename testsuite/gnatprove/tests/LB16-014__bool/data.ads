package Data is

   subtype T_Boolean is Boolean;
   type T_Nat32 is range 0 .. (2 ** 32 - 1);
   type T_Data_Type is (Boolean_Type, Nat32_Type);
   type T_Strong_Data_Type(Data_Type : T_Data_Type := T_Data_Type'First) is private;

   function Is_Nat32(Strong_Data_Type : T_Strong_Data_Type) return T_Boolean;

   function Get_Min_Nat32(Strong_Data_Type : T_Strong_Data_Type) return T_Nat32
   with Pre => Is_Nat32(Strong_Data_Type);

   function Create_Type(Min : in T_Nat32) return T_Strong_Data_Type
   with Post => (Is_Nat32(Create_Type'Result) and then
                 Min = Get_Min_Nat32(Create_Type'Result));

private

   type T_Strong_Data_Type(Data_Type : T_Data_Type := T_Data_Type'First) is
      record
         case Data_Type is
            when Data.Boolean_Type =>
               null;
            when Data.Nat32_Type =>
               Min_Nat32     : T_Nat32;
         end case;
      end record;

   function Is_Nat32(Strong_Data_Type : T_Strong_Data_Type) return T_Boolean
   is (Strong_Data_Type.Data_Type = Nat32_Type);

   function Get_Min_Nat32(Strong_Data_Type : T_Strong_Data_Type) return T_Nat32
   is (Strong_Data_Type.Min_Nat32);

   function Create_Type(Min : in T_Nat32) return T_Strong_Data_Type
   is (T_Strong_Data_Type'(Data_Type => Nat32_Type,
                           Min_Nat32 => Min));

end Data;
