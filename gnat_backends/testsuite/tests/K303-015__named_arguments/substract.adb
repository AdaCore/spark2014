package body Substract is
   function Sub (First : Integer; Second : Integer) return Integer is
   begin
      return First - Second;
   end Sub;

   function OppSub (First : Integer; Second : Integer) return Integer is
   begin
      return Sub (First => Second, Second => First);
   end OppSub;
end Substract;
