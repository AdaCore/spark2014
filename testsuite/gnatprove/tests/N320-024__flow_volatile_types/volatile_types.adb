package body Volatile_Types is
   procedure Good_Read (Value : out Integer) is
   begin
      Value := Integer (Vol);
   end Good_Read;

   procedure Bad_Read (Value : out Integer) is
   begin
      Value := Integer (Vol);
   end Bad_Read;

   procedure Local_Vol (Value : out Integer) is
      type Local_Volatile_T is range 1 .. 2
        with Volatile;

      L_Vol : Local_Volatile_T;  --  Problem!! Volatile objects must be
                                 --  declared at library level.
   begin
      Value := Integer (L_Vol);
   end Local_Vol;
end Volatile_Types;
