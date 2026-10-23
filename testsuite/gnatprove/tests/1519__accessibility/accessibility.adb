procedure Accessibility with SPARK_Mode is
   function Id (X : not null access constant Integer)
     return not null access constant Integer is (X) with Global => null;

   function Choose (X : not null access constant Integer; B : Boolean)
     return not null access constant Integer with Global => null
   is
      Local : access constant Integer := Id (X);
   begin
      --  The first alternative has a local master. This failure is deliberate.
      return (if B then Id (Local) else Local); -- @ACCESSIBILITY_CHECK:FAIL
   end Choose;
begin
   null;
end Accessibility;
