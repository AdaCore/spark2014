package body Device is

   procedure Stabilize (Mode    : in Mode_T;
                        Success : out Boolean)
   is
   begin
      if Accel < Giro then
         Rotors := Rotors + 5.0;
         Success := True;
      else
         Success := False;
      end if;
   end Stabilize;

   procedure Try_Stabilize (Mode_First : in Mode_T;
                            Mode_Last  : in Mode_T)
   with SPARK_Mode => On
   is
      Success : Boolean;
   begin
      for Mode in Mode_First .. Mode_Last loop
         Stabilize (Mode, Success);
         exit when Success;
      end loop;
   end Try_Stabilize;

end Device;
