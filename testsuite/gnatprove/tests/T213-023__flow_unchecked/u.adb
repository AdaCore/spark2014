with Ada.Unchecked_Conversion;

procedure U (X : Integer; Y : out Integer) is

   function Convert is new Ada.Unchecked_Conversion
     (Source => Integer, Target => Integer);

begin
   Y := Convert (Convert (X));
end;
