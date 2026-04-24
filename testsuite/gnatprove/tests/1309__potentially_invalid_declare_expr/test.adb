pragma Ada_2022;

procedure Test with SPARK_Mode is

   function F return Positive
   with Global => null, Potentially_Invalid => F'Result, Import;

   V : Natural :=
     (declare
        C : constant Positive := F
        with Potentially_Invalid;
      begin
        (if C'Valid then C else 0));
begin
   null;
end Test;
