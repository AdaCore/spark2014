with P2.Trace;
package body P2
  with SPARK_Mode => On
is

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

end P2;





