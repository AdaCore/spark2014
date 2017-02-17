package body P
  with SPARK_Mode => On
is
   package Trace
   is
      procedure Put (S : String)
        with Global  => null,
             Depends => (null => S);
   end Trace;

   package body Trace is separate;

   procedure Op1 (X : in out Integer)
   is
   begin
      X := X + 1;
      --  this call should NOT appear to have a side-effect
      Trace.Put ("Hello");
   end Op1;

   procedure Op2 (X : in out Integer)
   is
   begin
      X := X + 1;
      --  this call should NOT appear to have a side-effect
      pragma Debug (Trace.Put ("Hello"));
   end Op2;

   function F1 (X : in Integer) return Integer
   is
      L : Integer;
   begin
      L := X;
      Op1 (L);
      return L;
   end F1;

   function F2 (X : in Integer) return Integer
   is
      L : Integer;
   begin
      L := X;
      Op2 (L);
      return L;
   end F2;

end P;





