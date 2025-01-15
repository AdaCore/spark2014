pragma Extensions_Allowed (On);

procedure Test with SPARK_Mode is

   E : exception;

   function Raise_Exc return Boolean with
     Import,
     Global => null,
     Side_Effects,
     Always_Terminates,
     Exceptional_Cases => (E => True);

   procedure P with
     Exceptional_Cases => (E => True);

   procedure P is
   begin
      C : Boolean := Raise_Exc with Ghost; --@RAISE:FAIL
      null;
   end P;

begin
   null;
end;
