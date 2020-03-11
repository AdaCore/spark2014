with Interfaces;

package body Test
is

   type Value_Type is new Interfaces.Unsigned_64
   with
      Size => 128;

   subtype Index_Type is Integer range 1 .. 10;

   type Array_Type is array (Index_Type) of Value_Type;

   Global_Values : Array_Type
   with
      Volatile,
      Import;

   Local : Array_Type := (others => 0);

   -----------------------------------------------------------------------------

   procedure Get (Index : out Integer)
   is
      Temp_Value : Value_Type;
   begin
      Index := 0;
      for S in Index_Type loop
         Temp_Value := Global_Values (S);
         if Temp_Value > Local (S) then
            Index := S;
            Local (S) := Temp_Value;
            exit;
         end if;
      end loop;
   end Get;

end Test;
