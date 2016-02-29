package body Fileio with SPARK_Mode is

   procedure Simple (X, Y : in out Integer) is
      Z : Boolean := X > Y;
   begin
      if Z then
         raise Constraint_Error;
      end if;
      X := X + 1;
      Y := Y + 1;
   end Simple;

   procedure Getc (File : File_Type; Ch : out Int) is
   begin
      fgetc (File.Descr, ch);

      if ch = EOF and then ferror (File.Descr) /= 0 then
         raise Device_Error;
      end if;
   end Getc;

   procedure Ungetc (ch : int; File : File_Type) is
      Result : Int;
   begin
      if ch /= EOF then
         ungetc (ch, File.Descr, Result);
         if result = EOF then
            raise Device_Error;
         end if;
      end if;
   end Ungetc;

end Fileio;
