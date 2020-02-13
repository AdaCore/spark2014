with Ada.Unchecked_Conversion;

procedure W (X : Integer; Y : out Integer)
   with Global => null
is
   function Convert is new Ada.Unchecked_Conversion
     (Source => Integer, Target => Integer);

begin
   Y := Convert (Convert (X));
end;
