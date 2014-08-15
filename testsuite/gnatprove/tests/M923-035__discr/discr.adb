procedure Discr is

   -- TU: 1. The type of a ``discriminant_specification`` shall be discrete.
   type I1 (I : access Integer) is record -- illegal
      null;
   end record;


   type Rect (I, J : Integer) is record
      null;
   end record;

   -- TU: 2. A ``discriminant_specification`` shall not occur as part of a
   --     derived type declaration.
   type Square (K : Integer) is new Rect(K,K); -- illegal discrimiant renaming

   procedure P (X : in Rect) is
      Y : Square := Square(X);  --  BAD
   begin
      null;
   end;
   X : Rect(1,2);
begin
   P (X);
end Discr;
