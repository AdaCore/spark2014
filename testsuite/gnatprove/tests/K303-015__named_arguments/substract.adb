package body Substract is
   function Sub (First : Integer; Second : Integer) return Integer is
   begin
      return First - Second;
   end Sub;

   function Add3 (First : Integer; Second : Integer; Third : Integer)
      return Integer is
   begin
      return First + Second + Third;
   end Add3;

   function SubSimp (First : Integer; Second : Integer) return Integer is
   begin
      return Sub (First, Second);
   end SubSimp;

   function OppSub (First : Integer; Second : Integer) return Integer is
   begin
      return Sub (First => Second, Second => First);
   end OppSub;

   function SubInv (First : Integer; Second : Integer) return Integer is
   begin
      return Sub (Second => Second, First => First);
   end SubInv;

   function AddPart return Integer is
   begin
      return Add3 (1, Third => 3, Second => 2);
   end AddPart;
end Substract;
