package body Subprograms is
   function F1 (Val : Integer) return Integer is
   begin
      return Val * 0;
   end F1;

   function F1bis (Val : Integer) return Integer is
   begin
      return F1 (Val);
   end F1bis;

   function F2 (Val : Integer) return Integer is
   begin
      if Val = 0 then
         return 1;
      else
         return Val / Val;
      end if;
   end F2;

   function F2bis (Val : Integer) return Integer is
   begin
      return F2 (Val);
   end F2bis;

   function F3 (Val : Integer) return Integer is
   begin
      return Val;
   end F3;

   function F3bis (Val : Integer) return Integer is
   begin
      return 2 - Val;
   end F3bis;

   procedure Incr (Val : in out Integer) is
   begin
      Val := Val + 1;
   end Incr;

end Subprograms;
