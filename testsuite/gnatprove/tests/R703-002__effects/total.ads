package Total is

   type Enum is (A, B, C);
   type Enum_List is array (Enum) of Enum;
   Ctxt : Enum_List;

   function Compute
     (In_Ctxt : in Enum)
      return Natural;

end Total;
