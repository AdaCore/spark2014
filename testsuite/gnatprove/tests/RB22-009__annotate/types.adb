package body Types
   with SPARK_Mode
is

   function Foo (Buffer : Bytes) return Int is
      Result : Int := 0;
      I : Natural := 0;
   begin
      while I < Buffer'Length
      loop
         Result := Result + Int (Buffer (Buffer'First + I));
         I := I + 1;
      end loop;
      return Result;
   end Foo;

end Types;
