package C413005P is
   type TP is tagged record
      Data : Integer := 999;
   end record;

   procedure Set (X : in out TP; Value : in Integer);

end C413005P;
