package C413005P is
   type TP is tagged record
      Data : Integer := 999;
   end record;

   procedure Set (X : in out TP; Value : in Integer);
   function Get (X : TP) return Integer;

   procedure Class_Wide_Set (X : in out TP'Class; Value : Integer);
   function Class_Wide_Get (X : TP'Class) return Integer;

end C413005P;
